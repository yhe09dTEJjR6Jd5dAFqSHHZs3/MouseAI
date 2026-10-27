import os
import sys
import io
import math
import time
import random
import gzip
import json
import queue
import struct
import ctypes
import threading
import subprocess
import importlib
import shutil
import re
import copy
import contextlib
import hashlib
import urllib.request
import multiprocessing as mp
from pathlib import Path
from collections import deque
import tkinter as tk
from tkinter import ttk, filedialog

VIS_W = 128
VIS_H = 72
PIXELS = VIS_W * VIS_H
CHANNELS = 3
VIS_N = PIXELS * CHANNELS * 2
CTRL_N = 8
META_N = 20
MAX_REPLAY_RECORDS = max(1024, int(math.sqrt(max(1, (os.cpu_count() or 1) * 1024 * 1024))))
REPLAY_MAGIC = b'MOUSEAI8'
REPLAY_PACK = struct.Struct('<BBf?ff?' + 'f' * (META_N * 2 + CTRL_N * 2))

def replay_capacity():
    available = 0
    if os.name == 'nt':
        try:
            amount = ctypes.c_ulonglong()
            if ctypes.WinDLL('kernel32').GetPhysicallyInstalledSystemMemory(ctypes.byref(amount)):
                available = amount.value * 1024
        except (OSError, AttributeError):
            pass
    elif hasattr(os, 'sysconf'):
        try:
            available = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
        except (OSError, ValueError):
            pass
    if not available:
        return MAX_REPLAY_RECORDS
    sample_size = VIS_N * 2 + REPLAY_PACK.size
    budget = available / sample_size
    return max(64, int(min(budget * .035, math.sqrt(budget) * math.sqrt(max(1, os.cpu_count() or 1)))))

REPLAY_LIMIT = replay_capacity()
ACT = [(0, 0, 0, '', 0)]
for magnitude in (.3, .7):
    for angle in range(8):
        a = angle * math.tau / 8
        ACT.append((math.cos(a), math.sin(a), magnitude, '', 0))
ACT += [(0, 0, 0, 'l+', 0), (0, 0, 0, 'l-', 0), (0, 0, 0, 'r+', 0), (0, 0, 0, 'r-', 0), (0, 0, 0, 'm+', 0), (0, 0, 0, 'm-', 0), (0, 0, 0, '', .5), (0, 0, 0, '', -.5), (0, 0, 0, '', 1.), (0, 0, 0, '', -1.)]
ACT_N = len(ACT)

def speed_reference(region, dt):
    _, _, w, h = region
    diagonal = math.hypot(w, h)
    return diagonal / max(math.sqrt(max(.001, dt)), 1.)

def adaptive_exploration(steps, updates, uncertainty=1.):
    learned = max(0., updates) / math.sqrt(1. + max(0., steps))
    return max(0., min(1., uncertainty / math.sqrt(1. + learned)))

class AnyStop:
    def __init__(self, *events):
        self.events = events

    def is_set(self):
        return any(event.is_set() for event in self.events)

    def wait(self, timeout):
        if self.is_set():
            return True
        if self.events:
            self.events[0].wait(timeout)
        return self.is_set()


def candidates(held):
    allowed = list(range(17))
    for i, (b, press) in enumerate((('l', True), ('l', False), ('r', True), ('r', False), ('m', True), ('m', False)), 17):
        if bool(held.get(b, False)) != press:
            allowed.append(i)
    allowed.extend(range(23, ACT_N))
    return allowed


def explore_action(allowed, meta=None, steps=0):
    if not allowed:
        return 0
    if meta is None:
        return random.choice(allowed)
    change = max(0., float(meta[16]))
    held = sum(float(meta[i]) > .5 for i in (9, 10, 11))
    scores = []
    for action in allowed:
        _, _, speed, button, wheel = ACT[action]
        activity = abs(speed) + abs(wheel) + bool(button)
        penalty = (1. + held) if button and button.endswith('+') else 1.
        scores.append((1. + change) / (1. + activity * penalty))
    return random.choices(allowed, weights=scores, k=1)[0]


def normalize_control(values):
    ctrl = [float(v) if math.isfinite(float(v)) else 0. for v in values]
    if len(ctrl) != CTRL_N:
        raise ValueError('连续鼠标动作长度错误')
    ctrl = [max(-1., min(1., value)) for value in ctrl]
    norm = math.hypot(ctrl[0], ctrl[1])
    if norm > 1.:
        ctrl[0], ctrl[1] = ctrl[0] / norm, ctrl[1] / norm
    ctrl[2] = max(0., ctrl[2])
    ctrl[7] = max(0., ctrl[7])
    return tuple(ctrl)


def anchor_control(action, prediction=None, trust=0.):
    ax, ay, speed, button, wheel = ACT[action]
    control = [float(ax), float(ay), float(speed), 0., 0., 0., float(wheel), .5]
    if button:
        control[{'l': 3, 'r': 4, 'm': 5}[button[0]]] = 1. if button[1] == '+' else -1.
    if prediction is not None:
        trust = max(0., min(1., float(trust)))
        prediction = normalize_control(prediction)
        control = [(1. - trust) * old + trust * new for old, new in zip(control, prediction)]
    return normalize_control(control)


def exploratory_control(action, meta=None):
    ctrl = list(anchor_control(action))
    if random.random() < .5 or action == 0:
        angle = random.uniform(-math.pi, math.pi)
        strength = random.betavariate(1.5, 2.)
        ctrl[0], ctrl[1], ctrl[2] = math.cos(angle), math.sin(angle), strength
    if random.random() < .35:
        ctrl[6] = random.uniform(-1., 1.)
    held = {key: bool(meta[index] > .5) if meta is not None else False for key, index in (('l', 9), ('r', 10), ('m', 11))}
    for key, index in (('l', 3), ('r', 4), ('m', 5)):
        if ctrl[index] == 0. and random.random() < .18:
            ctrl[index] = -1. if held[key] else 1.
    ctrl[7] = random.betavariate(2., 2.)
    return normalize_control(ctrl)

def sleep_split(records):
    held_out = [i for i, row in enumerate(records) if row[12]]
    if not held_out:
        return None
    runs = []
    first = last = held_out[0]
    for index in held_out[1:]:
        if index != last + 1:
            runs.append((first, last))
            first = index
        last = index
    runs.append((first, last))
    typical = sorted(end - start + 1 for start, end in runs)[len(runs) // 2]
    guard = max(2, int(math.sqrt(max(1, typical))))
    excluded = bytearray(len(records))
    for start, end in runs:
        excluded[max(0, start - guard):min(len(records), end + guard + 1)] = b'\x01' * (min(len(records), end + guard + 1) - max(0, start - guard))
    training = [row for i, row in enumerate(records) if not excluded[i] and not row[12]]
    validation = [records[i] for i in held_out]
    minimum = max(8, int(math.sqrt(len(records))))
    if min(len(training), len(validation)) < minimum:
        return None
    return training, validation


def quarantine(path):
    if path.exists():
        try:
            os.replace(path, path.with_name(path.name + '.damaged'))
        except OSError:
            pass

def session_signature(image):
    chunks = bytearray()
    for scale in range(1):
        for y in range(0, VIS_H, 9):
            for x in range(0, VIS_W, 16):
                colors = []
                for channel in range(CHANNELS):
                    base = (scale * CHANNELS + channel) * PIXELS
                    colors.append(sum(sum(image[base + (y + j) * VIS_W + x:base + (y + j) * VIS_W + x + 16]) for j in range(9)) // 144)
                chunks.extend(colors)
    return hashlib.blake2s(chunks, digest_size=8).digest()


class Feedback:
    def __init__(self):
        self.frequency = {}
        self.sequence = deque(maxlen=32)
        self.background = None
        self.variance = 0.
        self.total = 0
        self.effects = 0
        self.blocks = 0
        self.repeats = 0
        self.dynamics = {}
        self.passive_average = 0.
        self.passive_variance = 0.
        self.passive_count = 0
        self.prediction_error = 0.
        self.predictable_effects = 0
        self.transition_frequency = {}
        self.recent_states = deque(maxlen=max(4, int(math.sqrt(REPLAY_LIMIT))))
        self.progress_effects = 0
        self.efficacy_total = 0.
        self.stagnant = 0
        try:
            self.numpy = importlib.import_module('numpy')
        except ImportError:
            self.numpy = None

    def difference(self, left, right):
        size = PIXELS * CHANNELS
        if self.numpy is not None:
            np = self.numpy
            a = np.frombuffer(left, dtype=np.uint8, count=size).astype(np.int16)
            b = np.frombuffer(right, dtype=np.uint8, count=size).astype(np.int16)
            return float(np.abs(a - b).mean()) / 255.
        return sum(abs(a - b) for a, b in zip(left[:size], right[:size])) / (size * 255.)

    def assess(self, old, new, previous, outcome, pointer, region):
        dist = self.difference(old, new)
        bg = self.difference(previous, old)
        count = self.total + 1
        rate = 1. / math.sqrt(count)
        if self.background is None:
            self.background = bg
        delta = bg - self.background
        self.background += rate * delta
        self.variance += rate * (delta * delta - self.variance)
        noise = max(0., self.background) + math.sqrt(max(0., self.variance))
        changed = bool(outcome['changed'])
        if not changed and not outcome['blocked']:
            self.passive_count += 1
            passive_rate = 1. / math.sqrt(self.passive_count)
            passive_diff = dist - self.passive_average
            self.passive_average += passive_rate * passive_diff
            self.passive_variance += passive_rate * (passive_diff * passive_diff - self.passive_variance)
        natural = self.passive_average + math.sqrt(max(0., self.passive_variance))
        baseline = max(bg, noise, natural)
        impact = max(0., dist - baseline)
        signature = session_signature(new)
        old_signature = session_signature(old)
        sightings = self.frequency.get(signature, 0)
        self.frequency[signature] = sightings + 1
        if len(self.frequency) > REPLAY_LIMIT:
            for key in sorted(self.frequency, key=self.frequency.get)[:max(1, len(self.frequency) // 4)]:
                self.frequency.pop(key, None)
        requested = int(outcome.get('requested_action', outcome['action']))
        executed = int(outcome['action'])
        intended = outcome.get('intended_ctrl', outcome['ctrl'])
        signature_control = bytes(max(0, min(15, round((float(v) + 1.) * 7.5))) for v in intended)
        self.sequence.append((old_signature, signature_control))
        repetition = self.sequence.count(self.sequence[-1]) / len(self.sequence)
        x, y, w, h = region
        cx = (pointer[0] - x) / max(1, w)
        cy = (pointer[1] - y) / max(1, h)
        at_edge = min(cx, cy, 1. - cx, 1. - cy) <= 0.
        efficacy = max(0., min(1., float(outcome.get('efficacy', 1.))))
        minimum = 1. / (PIXELS * CHANNELS * 255.)
        signal = changed and impact > max(minimum, noise / math.sqrt(count))
        context = hashlib.blake2s(old_signature, digest_size=3).digest()
        dynamics_key = (context, signature_control)
        prediction, uncertainty, seen = self.dynamics.get(dynamics_key, (0., max(noise, minimum), 0))
        deviation = abs(impact - prediction)
        relative_error = deviation / max(uncertainty + noise, minimum)
        surprise = math.tanh(relative_error)
        predictable = max(0., 1. - relative_error)
        causal = impact
        agreement = min(1., causal / max(dist, minimum)) if signal else 0.
        if signal and outcome['moved'] and not outcome['switches'] and not outcome['scroll']:
            activity = outcome['moved'] / max(1., math.hypot(region[2], region[3]))
            agreement *= 1. / (1. + activity / max(minimum, impact))
        novelty = 1. / math.sqrt(1. + sightings)
        consistency = predictable if seen else novelty
        transition = (old_signature, signature)
        previous_transition_count = self.transition_frequency.get(transition, 0)
        self.transition_frequency[transition] = previous_transition_count + 1
        if len(self.transition_frequency) > REPLAY_LIMIT:
            for key in sorted(self.transition_frequency, key=self.transition_frequency.get)[:max(1, len(self.transition_frequency) // 4)]:
                self.transition_frequency.pop(key, None)
        lookback = len(self.recent_states)
        repeated_state = self.recent_states.count(signature) / max(1, lookback)
        loop = lookback > 1 and old_signature != signature and (signature == self.recent_states[-2] or repeated_state > 1. / math.sqrt(lookback))
        progress = float(signal and old_signature != signature and not loop and predictable >= surprise)
        transition_novelty = 1. / math.sqrt(1. + previous_transition_count)
        progress_gain = progress * agreement * efficacy * transition_novelty
        self.stagnant = 0 if progress else self.stagnant + 1
        self.recent_states.append(signature)
        gain = agreement * consistency * efficacy * (1. if signal else 0.) + progress_gain
        penalty = (1. - efficacy) * float(any(abs(v) > .08 for v in intended[:7]))
        penalty += float(loop) * repeated_state * (1. + float(not signal))
        penalty += float(changed and not signal) * min(1., self.stagnant / math.sqrt(1. + self.total))
        penalty += float(bool(outcome['blocked']))
        penalty += max(0., surprise - consistency) * agreement / math.sqrt(1. + seen)
        penalty += repetition * float(not signal) / math.sqrt(1. + seen)
        penalty += (1. - efficacy) * agreement
        penalty += float(at_edge) * float(outcome['moved'] > 0.)
        reward = math.tanh(gain - penalty)
        update_rate = 1. / math.sqrt(1. + seen)
        expected = prediction + update_rate * (impact - prediction)
        spread = uncertainty + update_rate * (deviation - uncertainty)
        self.dynamics[dynamics_key] = (expected, max(minimum, spread), seen + 1)
        if len(self.dynamics) > REPLAY_LIMIT:
            for key in sorted(self.dynamics, key=lambda k: self.dynamics[k][2])[:max(1, len(self.dynamics) // 4)]:
                self.dynamics.pop(key, None)
        self.prediction_error += deviation
        self.predictable_effects += int(bool(signal and seen and predictable > surprise))
        self.total += 1
        self.effects += int(signal)
        self.blocks += int(bool(outcome['blocked']))
        self.repeats += int(repetition > 1. / math.sqrt(len(self.sequence)) or loop)
        self.progress_effects += int(bool(progress))
        self.efficacy_total += efficacy
        return reward, dist, bool(progress)


def read_replay(folder, slot):
    path = folder / f'experience.{slot}.gz'
    records = deque(maxlen=REPLAY_LIMIT)
    try:
        digest = hashlib.sha256()
        with gzip.open(path, 'rb') as f:
            head = f.read(len(REPLAY_MAGIC) + 12)
            if len(head) != len(REPLAY_MAGIC) + 12 or head[:len(REPLAY_MAGIC)] != REPLAY_MAGIC:
                raise ValueError('经验文件版本错误')
            digest.update(head)
            count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
            if count > max(REPLAY_LIMIT * 8, 1024) or generation < 1:
                raise ValueError('经验标头异常')
            for _ in range(count):
                raw = f.read(REPLAY_PACK.size)
                ob, nxt = f.read(VIS_N), f.read(VIS_N)
                if len(raw) != REPLAY_PACK.size or len(ob) != VIS_N or len(nxt) != VIS_N:
                    raise ValueError('经验数据不完整')
                digest.update(raw)
                digest.update(ob)
                digest.update(nxt)
                values = REPLAY_PACK.unpack(raw)
                action, executed_action, reward, done, dt, efficacy, reserved = values[:7]
                numeric = values[7:]
                if action >= ACT_N or executed_action >= ACT_N or not math.isfinite(reward) or not .001 <= dt <= 2. or not 0. <= efficacy <= 1. or not all(math.isfinite(v) for v in numeric):
                    raise ValueError('经验数值无效')
                meta = tuple(numeric[:META_N])
                nmeta = tuple(numeric[META_N:META_N * 2])
                ctrl = tuple(numeric[META_N * 2:META_N * 2 + CTRL_N])
                intended = tuple(numeric[META_N * 2 + CTRL_N:])
                records.append((ob, meta, action, nxt, nmeta, float(reward), bool(done), float(dt), ctrl, intended, executed_action, float(efficacy), bool(reserved)))
            if f.read(32) != digest.digest() or f.read(1):
                raise ValueError('经验校验失败')
        return records, generation
    except (OSError, EOFError, ValueError, struct.error, MemoryError):
        return None


def replay_sources(folder):
    for slot in (0, 1, 'recovery'):
        pair = read_replay(folder, slot)
        if pair is not None:
            yield pair[1], slot, pair[0]


def discard_recovery(folder, generation):
    path = folder / 'experience.recovery.gz'
    try:
        with gzip.open(path, 'rb') as source:
            header = source.read(len(REPLAY_MAGIC) + 12)
        if len(header) == len(REPLAY_MAGIC) + 12 and header.startswith(REPLAY_MAGIC):
            _, recovered_generation = struct.unpack('<IQ', header[len(REPLAY_MAGIC):])
            if recovered_generation <= generation:
                path.unlink(missing_ok=True)
    except (OSError, ValueError, EOFError, struct.error):
        pass


def save_replay(folder, records, slot, generation):
    path = folder / f'experience.{slot}.gz'
    tmp = folder / f'experience.{slot}.gz.tmp'
    digest = hashlib.sha256()
    entries = list(records)
    try:
        with open(tmp, 'wb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', compresslevel=1) as f:
                head = REPLAY_MAGIC + struct.pack('<IQ', len(entries), generation)
                f.write(head)
                digest.update(head)
                for ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved in entries:
                    record = REPLAY_PACK.pack(action, executed_action, reward, done, dt, efficacy, reserved, *meta, *nmeta, *ctrl, *intended)
                    for payload in (record, ob, nxt):
                        f.write(payload)
                        digest.update(payload)
                f.write(digest.digest())
            raw.flush()
            os.fsync(raw.fileno())
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            try:
                tmp.unlink()
            except OSError:
                pass

def read_json(path, default):
    try:
        with gzip.open(path, 'rt', encoding='utf-8') as f:
            return json.load(f)
    except (OSError, ValueError, UnicodeError):
        if path.exists():
            quarantine(path)
        return default


def save_json(path, obj):
    tmp = Path(str(path) + '.tmp')
    try:
        with open(tmp, 'wb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', compresslevel=2) as compressed:
                with io.TextIOWrapper(compressed, encoding='utf-8') as f:
                    json.dump(obj, f, ensure_ascii=False, separators=(',', ':'))
            raw.flush()
            os.fsync(raw.fileno())
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            try:
                tmp.unlink()
            except OSError:
                pass


class LiteBrain:
    def __init__(self, folder):
        self.folder = folder
        self.table = {}
        self.actor = {}
        self.visits = {}
        self.steps = 0
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.generation = 0
        self.latest_replay_generation = 0
        self.slot = -1
        self.label = 'CPU · 自适应轻量后端'
        self.accelerated = False
        self.train_memory = None
        self.sleep_evaluation = None
        self.sleep_best = None
        self.save_lock = threading.RLock()
        self.checkpoint_lock = threading.Lock()
        recovered = list(replay_sources(folder))
        for generation, slot, records in sorted(recovered, key=lambda row: (row[0], row[1] == 'recovery'), reverse=True):
            data = read_json(folder / f'learning.{slot}.lite.gz', {})
            if not isinstance(data, dict) or data.get('version') != 12 or data.get('generation') != generation or data.get('replay_count', len(records)) != len(records):
                continue
            table = {}
            actor = {}
            visits = {}
            for key, value in (data.get('table') or {}).items() if isinstance(data.get('table'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    numbers = [float(v) for v in value]
                    if len(keybytes) in (133, 14, 13) and len(numbers) == ACT_N and all(map(math.isfinite, numbers)):
                        table[keybytes] = numbers
                except (TypeError, ValueError, OverflowError):
                    continue
            for key, value in (data.get('actor') or {}).items() if isinstance(data.get('actor'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    numbers = [float(v) for v in value]
                    if len(keybytes) in (134, 15, 14) and len(numbers) == CTRL_N and all(math.isfinite(v) and -1. <= v <= 1. for v in numbers):
                        actor[keybytes] = list(normalize_control(numbers))
                except (TypeError, ValueError, OverflowError):
                    continue
            for key, value in (data.get('visits') or {}).items() if isinstance(data.get('visits'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    if len(keybytes) in (133, 14, 13) and isinstance(value, int) and not isinstance(value, bool) and value >= 0:
                        visits[keybytes] = value
                except (TypeError, ValueError, OverflowError):
                    continue
            try:
                steps = max(0, int(data.get('steps', 0)))
            except (TypeError, ValueError, OverflowError):
                continue
            self.table, self.actor, self.visits = table, actor, visits
            self.steps = steps
            self.memory, self.generation, self.slot = records, generation, slot if isinstance(slot, int) else -1
            break
        if recovered:
            generation, slot, records = max(recovered, key=lambda item: (item[0], item[1] == 'recovery'))
            self.latest_replay_generation = generation
            if generation != self.generation:
                self.memory = records
                self.slot = slot if isinstance(slot, int) else -1
                self.rebuild_from_memory()
            self.steps = max(self.steps, len(records))
        elif not self.table:
            self.steps = 0
        if self.memory and not self.table:
            self.rebuild_from_memory()

    def rebuild_from_memory(self):
        with self.save_lock:
            self.table.clear()
            self.actor.clear()
            self.visits.clear()
            for row in self.memory:
                if not row[12]:
                    self.update(row)

    def restore_experience(self, records, steps):
        with self.save_lock:
            self.memory = deque(records, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.rebuild_from_memory()

    def key(self, ob, meta):
        out = []
        for scale in range(2):
            for r in range(0, VIS_H, 9):
                for c in range(0, VIS_W, 16):
                    sums = [0, 0, 0]
                    for channel in range(CHANNELS):
                        for y in range(r, r + 9):
                            start = (scale * CHANNELS + channel) * PIXELS + y * VIS_W + c
                            sums[channel] += sum(ob[start:start + 16])
                    colors = [v // 144 for v in sums]
                    luminance = (colors[0] * 77 + colors[1] * 150 + colors[2] * 29) // 256
                    out.append(min(7, luminance // 32) + (8 if colors[0] > colors[1] else 0) + (16 if colors[2] > colors[1] else 0))
        out.extend((min(3, max(0, int(meta[4] * 4))), min(3, max(0, int(meta[5] * 4))), int(meta[9] > .5), int(meta[10] > .5), int(meta[11] > .5)))
        return bytes(out)

    def keys(self, ob, meta):
        visual = self.key(ob, meta)
        quantized = bytes(min(15, max(0, int((float(value) + 1.) * 7.5))) for value in meta)
        tiles = [visual]
        groups = ((0, 1, 2, 3), (4, 5, 6, 7, 8), (9, 10, 11, 12, 13, 17), (14, 15, 16, 18, 19))
        for index, group in enumerate(groups):
            data = bytes([index]) + bytes(quantized[i] for i in group)
            tiles.append(b'T' + bytes([index]) + hashlib.blake2s(data + visual[index * 12:index * 12 + 12] + visual[PIXELS // 144 + index * 12:PIXELS // 144 + index * 12 + 12], digest_size=12).digest())
            tiles.append(b'U' + bytes([index]) + quantized[group[0]:group[0] + 1] + hashlib.blake2s(data, digest_size=10).digest())
        return tiles

    def values(self, ob, meta):
        values = [self.table[key] for key in self.keys(ob, meta) if key in self.table]
        if not values:
            return None
        return [sum(part[action] for part in values) / len(values) for action in range(ACT_N)]

    def choose(self, ob, meta, held):
        opts = candidates(held)
        with self.save_lock:
            q = self.values(ob, meta)
            keys = self.keys(ob, meta)
            visits = sum(self.visits.get(key, 0) for key in keys)
            epsilon = adaptive_exploration(self.steps, visits, 1. / math.sqrt(1. + len(keys) if q is not None else 1.))
            exploring = q is None or random.random() < epsilon
            if exploring:
                choice = explore_action(opts, meta, self.steps)
                return choice, exploratory_control(choice, meta)
            choice = max(opts, key=lambda i: q[i])
            controls = [(self.actor[k + bytes([choice])], self.visits.get(k, 0)) for k in keys if k + bytes([choice]) in self.actor]
            if controls:
                weight = sum(w for _, w in controls)
                predicted = [sum(vec[i] * w for vec, w in controls) / max(1, weight) for i in range(CTRL_N)]
                confidence = visits / (1. + visits)
                return choice, anchor_control(choice, predicted, confidence)
            return choice, anchor_control(choice)

    def update(self, row):
        ob, meta, action, nxt, nmeta, reward, done, dt = row[:8]
        before = self.values(ob, meta)
        after = self.values(nxt, nmeta)
        held = {'l': nmeta[9] > .5, 'r': nmeta[10] > .5, 'm': nmeta[11] > .5}
        future = max(after[i] for i in candidates(held)) if after else 0.
        target = reward + (0 if done else (.975 ** (dt / .075)) * future)
        baseline = before[action] if before is not None else 0.
        correction = (target - baseline) / math.sqrt(1. + self.visits.get(self.key(ob, meta), 0))
        for key in self.keys(ob, meta):
            value = self.table.setdefault(key, [0.] * ACT_N)
            value[action] += correction
            self.visits[key] = self.visits.get(key, 0) + 1
            if len(row) > 11 and reward > 0. and row[11] > 0.:
                actor_key = key + bytes([action])
                old = self.actor.get(actor_key, list(anchor_control(action)))
                efficacy = min(1., max(0., row[11]))
                rate = efficacy * max(0., reward) / math.sqrt(1. + self.visits[key])
                executed = anchor_control(action, row[8], 1.)
                intended = anchor_control(action, row[9], 1.)
                self.actor[actor_key] = [old[i] * (1. - rate) + (executed[i] * efficacy + intended[i] * (1. - efficacy)) * rate for i in range(CTRL_N)]
        if len(self.table) > REPLAY_LIMIT * len(self.keys(ob, meta)):
            for k in sorted(self.table, key=lambda key: self.visits.get(key, 0))[:max(1, len(self.table) // 8)]:
                self.table.pop(k, None)
                self.visits.pop(k, None)
                for action_key in list(self.actor):
                    if action_key[:-1] == k:
                        self.actor.pop(action_key, None)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False):
        row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved))
        with self.save_lock:
            self.memory.append(row)
            if not reserved:
                self.update(row)
            self.steps += 1

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.train_memory if self.train_memory is not None else (row for row in self.memory if not row[12]))
        if not source:
            return 0
        total = 0
        with self.save_lock:
            for _ in range(count):
                if stop.is_set():
                    break
                self.update(random.choice(source))
                total += 1
        return total

    def policy_metric(self, records):
        useful = [row for row in records if row[2] != 0 and row[5] != 0.]
        if len(useful) < 8:
            return None
        good = 0
        for row in useful:
            q = self.values(row[0], row[1]) or [0.] * ACT_N
            held = {'l': row[1][9] > .5, 'r': row[1][10] > .5, 'm': row[1][11] > .5}
            best = max(candidates(held), key=lambda a: q[a])
            good += (best == row[2]) if row[5] > 0. else (best != row[2])
        return good / len(useful)

    def validation_targets(self, records):
        labels = []
        for row in records:
            after = self.values(row[3], row[4])
            held = {'l': row[4][9] > .5, 'r': row[4][10] > .5, 'm': row[4][11] > .5}
            future = max(after[a] for a in candidates(held)) if after else 0.
            labels.append(row[5] + (0. if row[6] else (.975 ** (row[7] / .075)) * future))
        return labels

    def evaluate(self, records, labels):
        loss = 0.
        for row, target in zip(records, labels):
            values = self.values(row[0], row[1])
            error = abs((values[row[2]] if values is not None else 0.) - target)
            loss += .5 * error * error if error < 1. else error - .5
        return loss / max(1, len(records))

    def begin_sleep(self):
        with self.save_lock:
            self.train_memory = None
            self.sleep_evaluation = None
            self.sleep_best = None
            split = sleep_split(list(self.memory))
            if split is None:
                self.train_memory = []
                return
            self.train_memory, validation = split
            labels = self.validation_targets(validation)
            before = self.evaluate(validation, labels)
            quality = self.policy_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits))

    def sleep_progress(self):
        with self.save_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality, snapshot, previous_actor, previous_visits = self.sleep_evaluation
            after = self.evaluate(records, labels)
            current = self.policy_metric(records)
            tolerance = max(1e-6, abs(before) * .002)
            if math.isfinite(after) and after + tolerance < before and (quality is None or current is None or current + .015 >= quality):
                if self.sleep_best is None or after + tolerance < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits))
            return after

    def end_sleep(self):
        with self.save_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            after = self.sleep_progress()
            records, labels, before, quality, snapshot, previous_actor, previous_visits = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            current = self.policy_metric(records)
            if best is not None:
                self.table, self.actor, self.visits = best[2:5]
                return True, before, best[0], quality, best[1]
            self.table, self.actor, self.visits = snapshot, previous_actor, previous_visits
            degraded = not math.isfinite(after) or after > before + max(.0005, abs(before) * .08) or (quality is not None and current is not None and current + .015 < quality)
            return (False if degraded else None), before, after, quality, current

    def save(self):
        self.folder.mkdir(parents=True, exist_ok=True)
        with self.checkpoint_lock:
            with self.save_lock:
                memory = list(self.memory)
                generation = max(self.generation, self.latest_replay_generation) + 1
                slot = (self.slot + 1) % 2
                data = {'version': 12, 'generation': generation, 'steps': self.steps, 'replay_count': len(memory), 'table': {k.hex(): v[:] for k, v in self.table.items()}, 'actor': {k.hex(): v[:] for k, v in self.actor.items()}, 'visits': {k.hex(): v for k, v in self.visits.items()}}
            save_replay(self.folder, memory, slot, generation)
            save_json(self.folder / f'learning.{slot}.lite.gz', data)
            with self.save_lock:
                self.generation, self.latest_replay_generation, self.slot = generation, generation, slot
            discard_recovery(self.folder, generation)

class TorchBrain:
    def __init__(self, folder, torch, device, label):
        self.folder = folder
        self.t = torch
        self.d = device
        self.label = label
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.save_lock = threading.RLock()
        self.model_lock = threading.RLock()
        self.checkpoint_lock = threading.Lock()
        self.generation = 0
        self.slot = -1
        self.model_slot = -1
        self.model_generation = 0
        nn = torch.nn

        class Net(nn.Module):
            def __init__(self):
                super().__init__()
                self.vision = nn.Sequential(nn.Conv2d(CHANNELS * 2, 16, 5, stride=2, padding=2), nn.ReLU(), nn.Conv2d(16, 32, 3, stride=2, padding=1), nn.ReLU(), nn.Conv2d(32, 48, 3, stride=2, padding=1), nn.ReLU(), nn.AdaptiveAvgPool2d((4, 6)), nn.Flatten(), nn.Linear(48 * 4 * 6, 160), nn.ReLU())
                self.policy = nn.Sequential(nn.Linear(160 + META_N, 192), nn.GELU(), nn.Linear(192, ACT_N))
                self.control = nn.Sequential(nn.Linear(160 + META_N, 128), nn.GELU(), nn.Linear(128, ACT_N * CTRL_N), nn.Tanh())
                self.effect = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 160), nn.GELU(), nn.Linear(160, 1))
                self.execution = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 128), nn.GELU(), nn.Linear(128, 1), nn.Sigmoid())
                self.dynamics = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 192), nn.GELU(), nn.Linear(192, 160 + META_N))

            def forward(self, frames, meta):
                embedding = torch.cat((self.vision(frames), meta), dim=1)
                raw = self.control(embedding).reshape(-1, ACT_N, CTRL_N)
                outputs = torch.cat((raw[..., :2], (raw[..., 2:3] + 1.) * .5, raw[..., 3:7], (raw[..., 7:8] + 1.) * .5), dim=-1)
                return self.policy(embedding), outputs, embedding

            def effect_value(self, embedding, controls):
                return self.effect(torch.cat((embedding, controls), dim=-1)).squeeze(-1)

            def execute_value(self, embedding, controls):
                return self.execution(torch.cat((embedding, controls), dim=-1)).squeeze(-1)

            def next_features(self, embedding, controls):
                return self.dynamics(torch.cat((embedding, controls), dim=-1))

        if getattr(device, 'type', None) == 'cuda':
            torch.backends.cudnn.benchmark = True
            if hasattr(torch.backends.cuda.matmul, 'allow_tf32'):
                torch.backends.cuda.matmul.allow_tf32 = True
        self.use_bfloat16 = False
        self.perf = {'transfer_ms': 0., 'inference_ms': 0., 'batches': 0, 'training_examples': 0}
        if getattr(device, 'type', None) == 'cuda':
            try:
                self.use_bfloat16 = bool(torch.cuda.is_bf16_supported())
            except (AttributeError, RuntimeError):
                pass
        self.q = Net().to(device)
        if getattr(device, 'type', None) == 'cuda':
            self.q = self.q.to(memory_format=torch.channels_last)
        self.target = copy.deepcopy(self.q).to(device)
        self.target.eval()
        self.optq = torch.optim.AdamW(self.q.parameters(), lr=1. / (VIS_N + META_N), weight_decay=1. / VIS_N)
        memory_bytes = 0
        if getattr(device, 'type', None) == 'cuda':
            try:
                memory_bytes = torch.cuda.mem_get_info(device)[0]
            except Exception:
                pass
        if not memory_bytes:
            sample_budget = max(8, int(math.sqrt(REPLAY_LIMIT)))
        else:
            sample_budget = max(2, int(memory_bytes * .05 / max(1, VIS_N * 20)))
        if getattr(device, 'type', None) == 'cuda' and memory_bytes:
            interactive = max(1, min(REPLAY_LIMIT, sample_budget, int(math.sqrt(REPLAY_LIMIT))))
            sleeping = max(1, min(REPLAY_LIMIT, sample_budget))
            self.batch_sizes = {False: interactive, True: sleeping}
            self.batch_limits = {False: max(1, min(REPLAY_LIMIT, max(interactive * 2, sample_budget // 4))), True: max(1, min(REPLAY_LIMIT, sample_budget * 2))}
        else:
            self.batch_sizes = {False: max(1, min(REPLAY_LIMIT, sample_budget, int(math.sqrt(REPLAY_LIMIT)))), True: max(1, min(REPLAY_LIMIT, sample_budget * 2, int(math.sqrt(REPLAY_LIMIT) * 2)))}
            self.batch_limits = {False: max(1, self.batch_sizes[False] * 2), True: max(1, self.batch_sizes[True] * 2)}
        self.training_throughput = {False: 0., True: 0.}
        self.training_latency = {False: 0., True: 0.}
        self.gpu_train_started = 0.
        self.gpu_train_examples = 0
        self.gpu_train_batches = 0
        self.steps = 0
        self.grads = 0
        self.train_memory = None
        self.sleep_evaluation = None
        self.sleep_best = None
        replay_pairs = list(replay_sources(folder))
        if replay_pairs:
            self.generation, recovered_slot, self.memory = max(replay_pairs, key=lambda entry: (entry[0], entry[1] == 'recovery'))
            self.slot = recovered_slot if isinstance(recovered_slot, int) else -1
        replay_generations = {slot: generation for generation, slot, _ in replay_pairs if isinstance(slot, int)}
        replay_counts = {slot: len(records) for generation, slot, records in replay_pairs if isinstance(slot, int)}
        for slot in sorted(replay_generations, key=lambda index: replay_generations[index]):
            path = folder / f'model.{slot}.pt'
            if not path.exists():
                continue
            try:
                state = torch.load(path, map_location='cpu', weights_only=True)
                if state.get('version') != 12:
                    continue
                generation = int(state['generation'])
                if generation <= self.model_generation or generation != replay_generations[slot] or state.get('replay_count', replay_counts[slot]) != replay_counts[slot]:
                    continue
                before_q = copy.deepcopy(self.q.state_dict())
                before_target = copy.deepcopy(self.target.state_dict())
                before_opt = copy.deepcopy(self.optq.state_dict())
                try:
                    self.q.load_state_dict(state['q'], strict=True)
                    self.target.load_state_dict(state['target'], strict=True)
                    self.optq.load_state_dict(state['opt'])
                    for group in self.optq.state.values():
                        for key, value in group.items():
                            if torch.is_tensor(value):
                                group[key] = value.to(device)
                except Exception:
                    self.q.load_state_dict(before_q)
                    self.target.load_state_dict(before_target)
                    self.optq.load_state_dict(before_opt)
                    raise
                self.steps = max(0, int(state.get('steps', 0)))
                self.grads = max(0, int(state.get('grads', 0)))
                self.model_generation = generation
                self.model_slot = slot
            except Exception:
                continue
        self.steps = max(self.steps, len(self.memory))
        self.recovery_required = bool(self.memory and self.generation != self.model_generation)
        if self.recovery_required or (not self.model_generation and len(self.memory) >= max(8, self.batch_sizes[False])):
            self.reconstruct_from_memory()
        self.q.eval()

    def reconstruct_from_memory(self):
        with self.save_lock:
            records = [row for row in self.memory if not row[12]]
        if len(records) < 2:
            return 0
        budget = max(1, int(math.sqrt(len(records)) * math.log2(2 + len(records))))
        return self.train(budget, AnyStop())

    def restore_experience(self, records, steps):
        with self.save_lock:
            self.memory = deque(records, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, int(steps), len(self.memory))
        return self.reconstruct_from_memory()

    def autocast(self):
        if getattr(self.d, 'type', None) == 'cuda' and self.use_bfloat16:
            return self.t.autocast(device_type='cuda', dtype=self.t.bfloat16)
        return contextlib.nullcontext()

    def images(self, observations):
        started = time.monotonic()
        if any(len(im) != VIS_N for im in observations):
            raise ValueError('采集画面维度不匹配')
        raw = bytearray().join(observations)
        source = self.t.frombuffer(raw, dtype=self.t.uint8).reshape(len(observations), CHANNELS * 2, VIS_H, VIS_W)
        cuda = getattr(self.d, 'type', None) == 'cuda'
        if cuda and len(observations) > 1:
            try:
                source = source.pin_memory()
            except RuntimeError:
                pass
        target = source.to(device=self.d, dtype=self.t.float32, non_blocking=bool(cuda and source.is_pinned())).div_(255)
        if cuda:
            target = target.contiguous(memory_format=self.t.channels_last)
        elapsed = (time.monotonic() - started) * 1000.
        self.perf['transfer_ms'] += (elapsed - self.perf['transfer_ms']) / math.sqrt(1. + self.steps)
        return target

    def choose(self, ob, meta, held):
        allowed = candidates(held)
        epsilon = adaptive_exploration(self.steps, self.grads)
        if random.random() < epsilon:
            action = explore_action(allowed, meta, self.steps)
            return action, exploratory_control(action, meta)
        inference_started = time.monotonic()
        with self.model_lock:
            self.q.eval()
            with self.t.no_grad():
                with self.autocast():
                    q, output, embedding = self.q(self.images([ob]), self.t.tensor([meta], dtype=self.t.float32, device=self.d))
                    candidate = output[0]
                    expanded = embedding.expand(ACT_N, -1)
                    returns = self.q.effect_value(expanded, candidate)
                    likelihood = self.q.execute_value(expanded, candidate)
                    confidence = 1. - adaptive_exploration(self.steps, self.grads)
                    metric = q[0] + confidence * (returns * likelihood - returns.detach().mean())
                values = metric.float().cpu().tolist()
                action = max(allowed, key=lambda i: values[i])
                control = output[0, action].float().cpu().tolist()
                predicted_efficacy = float(likelihood[action].float().item())
                trust = confidence * predicted_efficacy / max(1e-7, predicted_efficacy + (1. - predicted_efficacy) * epsilon)
        elapsed = (time.monotonic() - inference_started) * 1000.
        self.perf['inference_ms'] += (elapsed - self.perf['inference_ms']) / math.sqrt(1. + self.steps)
        return action, anchor_control(action, control, trust)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False):
        with self.save_lock:
            self.memory.append((ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved)))
            self.steps += 1

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.train_memory if self.train_memory is not None else (row for row in self.memory if not row[12]))
        if len(source) < 2:
            return 0
        with self.model_lock:
            self.gpu_train_batches = 0
            self.gpu_train_examples = 0
            self.q.train()
            try:
                while not stop.is_set():
                    try:
                        return self._train_locked(count, stop, source)
                    except RuntimeError as error:
                        detail = str(error).lower()
                        if 'out of memory' not in detail or self.batch_sizes[self.train_memory is not None] <= 1:
                            raise
                        mode = self.train_memory is not None
                        self.batch_limits[mode] = min(self.batch_limits[mode], max(1, self.batch_sizes[mode] // 2))
                        self.batch_sizes[mode] = self.batch_limits[mode]
                        self.optq.zero_grad(set_to_none=True)
                        self.gpu_train_batches = 0
                        self.gpu_train_examples = 0
                        if getattr(self.d, 'type', None) == 'cuda':
                            self.t.cuda.empty_cache()
                return 0
            finally:
                self.q.eval()

    def _train_locked(self, count, stop, source):
        t = self.t
        count_done = 0
        sleeping = self.train_memory is not None
        for _ in range(count):
            if stop.is_set():
                break
            started = time.monotonic()
            batch = random.sample(source, min(self.batch_sizes[sleeping], len(source)))
            state = self.images([row[0] for row in batch])
            future = self.images([row[3] for row in batch])
            meta = t.tensor([row[1] for row in batch], dtype=t.float32, device=self.d)
            nmeta = t.tensor([row[4] for row in batch], dtype=t.float32, device=self.d)
            acts = t.tensor([row[2] for row in batch], dtype=t.long, device=self.d)
            rew = t.tensor([row[5] for row in batch], dtype=t.float32, device=self.d)
            done = t.tensor([row[6] for row in batch], dtype=t.float32, device=self.d)
            dt = t.tensor([row[7] for row in batch], dtype=t.float32, device=self.d)
            ctrl = t.tensor([row[8] for row in batch], dtype=t.float32, device=self.d)
            efficacy = t.tensor([row[11] for row in batch], dtype=t.float32, device=self.d)
            with self.autocast():
                qvalues, predicted_all, embedding = self.q(state, meta)
            values = qvalues.gather(1, acts.unsqueeze(1)).squeeze(1)
            predicted = predicted_all.gather(1, acts[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
            effectiveness = self.q.effect_value(embedding, ctrl)
            intended = t.tensor([row[9] for row in batch], dtype=t.float32, device=self.d)
            execution = self.q.execute_value(embedding, intended)
            with t.no_grad():
                online, _, _ = self.q(future, nmeta)
                mask = t.zeros_like(online, dtype=t.bool)
                for index, column in ((17, 9), (19, 10), (21, 11)):
                    down = nmeta[:, column] > .5
                    mask[:, index] = down
                    mask[:, index + 1] = ~down
                online = online.masked_fill(mask, -1e8)
                best = online.argmax(dim=1, keepdim=True)
                next_q, _, future_features = self.target(future, nmeta)
                after = next_q.gather(1, best).squeeze(1)
                discount = (.975 ** (dt / .075)) * (1 - done)
                targets = rew + discount * after
                effect_targets = rew
            temporal = t.nn.functional.smooth_l1_loss(values, targets)
            effect_loss = t.nn.functional.smooth_l1_loss(effectiveness, effect_targets)
            execution_loss = t.nn.functional.smooth_l1_loss(execution, efficacy)
            dynamics_loss = t.nn.functional.smooth_l1_loss(self.q.next_features(embedding, ctrl), future_features.detach())
            advantage = (rew - effectiveness.detach()).clamp(-1., 1.)
            good = t.sigmoid(advantage / rew.detach().std(unbiased=False).clamp(min=1e-4))
            desired = ctrl * efficacy[:, None] + intended * (1. - efficacy[:, None])
            auxiliary = ((predicted - desired).square().mean(dim=1) * good * efficacy).mean()
            for module in (self.q.effect, self.q.execution):
                for param in module.parameters():
                    param.requires_grad_(False)
            try:
                actor_gain = (self.q.effect_value(embedding.detach(), predicted) * self.q.execute_value(embedding.detach(), predicted)).mean()
            finally:
                for module in (self.q.effect, self.q.execution):
                    for param in module.parameters():
                        param.requires_grad_(True)
            confidence = (1. - adaptive_exploration(self.steps, self.grads)) * rew.detach().std(unbiased=False).clamp(min=1e-5) / (rew.detach().std(unbiased=False).clamp(min=1e-5) + effect_loss.detach())
            dynamics_weight = (temporal.detach() + effect_loss.detach() + 1e-6) / (temporal.detach() + effect_loss.detach() + dynamics_loss.detach() + 1e-6)
            loss = temporal + effect_loss + execution_loss + auxiliary + dynamics_weight * dynamics_loss - confidence * actor_gain
            if not bool(t.isfinite(loss).item()):
                raise ValueError('模型训练数值异常')
            self.optq.zero_grad(set_to_none=True)
            loss.backward()
            t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.0)
            self.optq.step()
            self.grads += 1
            if not sleeping and self.grads % max(2, int(math.sqrt(max(1, self.steps)))) == 0:
                with t.no_grad():
                    for target_param, param in zip(self.target.parameters(), self.q.parameters()):
                        target_param.lerp_(param, .04)
            elapsed = max(.001, time.monotonic() - started)
            examples_measured = len(batch)
            if getattr(self.d, 'type', None) == 'cuda':
                if not self.gpu_train_batches:
                    self.gpu_train_started = started
                self.gpu_train_batches += 1
                self.gpu_train_examples += len(batch)
                if not sleeping or self.gpu_train_batches >= max(2, int(math.sqrt(max(1, self.steps)))) or stop.is_set() or _ == count - 1:
                    t.cuda.synchronize(self.d)
                    elapsed = max(.001, time.monotonic() - self.gpu_train_started)
                    examples_measured = self.gpu_train_examples
                    self.gpu_train_batches = 0
                    self.gpu_train_examples = 0
                else:
                    elapsed = None
            if elapsed is not None:
                self.perf['batches'] += 1
                self.perf['training_examples'] += examples_measured
                observed = examples_measured / elapsed
                latency = elapsed * len(batch) / max(1, examples_measured)
                previous_latency = self.training_latency[sleeping]
                previous = self.training_throughput[sleeping]
                self.training_throughput[sleeping] += (observed - previous) / math.sqrt(1. + self.grads)
                self.training_latency[sleeping] += (latency - self.training_latency[sleeping]) / math.sqrt(1. + self.grads)
                proposed = self.batch_sizes[sleeping]
                if previous > 0 and observed < previous / math.sqrt(2.):
                    proposed = max(1, int(proposed / math.sqrt(2.)))
                elif self.grads % max(2, int(math.sqrt(max(1, self.grads)))) == 0 and (not previous or observed >= previous or latency <= previous_latency):
                    proposed = max(proposed + 1, int(proposed * math.sqrt(1. + 1. / max(1, self.grads))))
                if getattr(self.d, 'type', None) == 'cuda':
                    try:
                        free, total = t.cuda.mem_get_info(self.d)
                        used = t.cuda.memory_allocated(self.d)
                        if free < max(used / max(1, len(batch)), total / max(1, self.batch_limits[sleeping])):
                            proposed = min(proposed, len(batch))
                    except RuntimeError:
                        pass
                self.batch_sizes[sleeping] = max(1, min(len(source), self.batch_limits[sleeping], proposed))
            count_done += 1
        return count_done

    def evaluate(self, entries, labels):
        self.q.eval()
        t = self.t
        total = 0.
        with t.no_grad():
            for start in range(0, len(entries), 24):
                segment = entries[start:start + 24]
                frames = self.images([row[0] for row in segment])
                meta = t.tensor([row[1] for row in segment], dtype=t.float32, device=self.d)
                actions = t.tensor([row[2] for row in segment], dtype=t.long, device=self.d)
                values, all_controls, features = self.q(frames, meta)
                qvalue = values.gather(1, actions.unsqueeze(1)).squeeze(1)
                target = t.tensor(labels[start:start + len(segment)], dtype=t.float32, device=self.d)
                controls = t.tensor([row[8] for row in segment], dtype=t.float32, device=self.d)
                intended = t.tensor([row[9] for row in segment], dtype=t.float32, device=self.d)
                efficacy = t.tensor([row[11] for row in segment], dtype=t.float32, device=self.d)
                rewards = t.tensor([row[5] for row in segment], dtype=t.float32, device=self.d)
                q_loss = t.nn.functional.smooth_l1_loss(qvalue, target, reduction='sum')
                selected_controls = all_controls.gather(1, actions[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
                teacher = (controls * efficacy[:, None] + intended * (1. - efficacy[:, None]))
                actor_loss = ((selected_controls - teacher).square().mean(dim=1) * efficacy).sum()
                effect_loss = t.nn.functional.smooth_l1_loss(self.q.effect_value(features, controls), rewards, reduction='sum')
                execution_loss = t.nn.functional.smooth_l1_loss(self.q.execute_value(features, intended), efficacy, reduction='sum')
                next_frames = self.images([row[3] for row in segment])
                next_meta = t.tensor([row[4] for row in segment], dtype=t.float32, device=self.d)
                next_features = self.target(next_frames, next_meta)[2]
                dynamics_loss = t.nn.functional.smooth_l1_loss(self.q.next_features(features, controls), next_features, reduction='none').mean(dim=1).sum()
                total += float((q_loss + effect_loss + execution_loss + dynamics_loss + actor_loss).cpu())
        return total / max(1, len(entries))

    def performance(self):
        with self.save_lock:
            training = self.training_throughput[self.train_memory is not None]
            return {'transfer_ms': round(self.perf['transfer_ms'], 3), 'inference_ms': round(self.perf['inference_ms'], 3), 'training_samples_per_second': round(training, 2), 'batches': self.perf['batches'], 'training_examples': self.perf['training_examples']}

    def effect_metric(self, records):
        if not records:
            return None
        t = self.t
        total = 0.
        with t.no_grad():
            for index in range(0, len(records), max(1, self.batch_sizes[True])):
                part = records[index:index + max(1, self.batch_sizes[True])]
                state = self.images([row[0] for row in part])
                meta = t.tensor([row[1] for row in part], dtype=t.float32, device=self.d)
                control = t.tensor([row[8] for row in part], dtype=t.float32, device=self.d)
                reward = t.tensor([row[5] for row in part], dtype=t.float32, device=self.d)
                features = self.q(state, meta)[2]
                total += float(t.nn.functional.smooth_l1_loss(self.q.effect_value(features, control), reward, reduction='sum').item())
        return total / len(records)

    def policy_metric(self, records):
        examples = [r for r in records if r[2] != 0 and r[5] != 0.]
        if len(examples) < 8:
            return None
        total = 0
        with self.t.no_grad():
            for start in range(0, len(examples), 24):
                part = examples[start:start + 24]
                q = self.q(self.images([r[0] for r in part]), self.t.tensor([r[1] for r in part], dtype=self.t.float32, device=self.d))[0].cpu().tolist()
                for row, scores in zip(part, q):
                    held = {'l': row[1][9] > .5, 'r': row[1][10] > .5, 'm': row[1][11] > .5}
                    chosen = max(candidates(held), key=lambda a: scores[a])
                    total += (chosen == row[2]) if row[5] > 0. else (chosen != row[2])
        return total / len(examples)

    def begin_sleep(self):
        with self.save_lock:
            records = list(self.memory)
        with self.model_lock:
            self.train_memory = None
            self.sleep_evaluation = None
            self.sleep_best = None
            split = sleep_split(records)
            if split is None:
                self.train_memory = []
                return
            self.train_memory, validation = split
            t = self.t
            labels = []
            self.q.eval()
            with t.no_grad():
                for start in range(0, len(validation), 24):
                    segment = validation[start:start + 24]
                    frames = self.images([row[3] for row in segment])
                    next_meta = t.tensor([row[4] for row in segment], dtype=t.float32, device=self.d)
                    online = self.q(frames, next_meta)[0]
                    mask = t.zeros_like(online, dtype=t.bool)
                    for index, column in ((17, 9), (19, 10), (21, 11)):
                        down = next_meta[:, column] > .5
                        mask[:, index] = down
                        mask[:, index + 1] = ~down
                    online = online.masked_fill(mask, -1e8)
                    best = online.argmax(dim=1, keepdim=True)
                    after = self.target(frames, next_meta)[0].gather(1, best).squeeze(1)
                    rewards = t.tensor([row[5] for row in segment], dtype=t.float32, device=self.d)
                    ends = t.tensor([row[6] for row in segment], dtype=t.float32, device=self.d)
                    durations = t.tensor([row[7] for row in segment], dtype=t.float32, device=self.d)
                    labels.extend((rewards + (1 - ends) * (.975 ** (durations / .075)) * after).cpu().tolist())
            before = self.evaluate(validation, labels)
            quality = self.policy_metric(validation)
            effect_before = self.effect_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads, effect_before)

    def sleep_progress(self):
        with self.model_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality = self.sleep_evaluation[:4]
            after = self.evaluate(records, labels)
            current = self.policy_metric(records)
            tolerance = max(1e-6, abs(before) * .002)
            effect_before = self.sleep_evaluation[8]
            effect_after = self.effect_metric(records)
            effect_ok = effect_before is None or (effect_after is not None and math.isfinite(effect_after) and effect_after <= effect_before + max(1e-6, abs(effect_before) * .02))
            if effect_ok and math.isfinite(after) and after + tolerance < before and (quality is None or current is None or current + .025 >= quality):
                if self.sleep_best is None or after + tolerance < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads)
            return after

    def end_sleep(self):
        with self.model_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            after = self.sleep_progress()
            records, labels, before, quality, old_q, old_target, old_opt, old_grads, old_effect = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            current = self.policy_metric(records)
            if best is not None:
                self.q.load_state_dict(best[2])
                self.target.load_state_dict(best[3])
                self.optq.load_state_dict(best[4])
                self.grads = best[5]
                return True, before, best[0], quality, best[1]
            self.q.load_state_dict(old_q)
            self.target.load_state_dict(old_target)
            self.optq.load_state_dict(old_opt)
            self.grads = old_grads
            degraded = not math.isfinite(after) or after > before + max(.002, abs(before) * .08) or (quality is not None and current is not None and current + .025 < quality)
            return (False if degraded else None), before, after, quality, current

    def save(self, checkpoint_generation=None, checkpoint_slot=None):
        self.folder.mkdir(parents=True, exist_ok=True)
        with self.checkpoint_lock:
            def cpu_copy(obj):
                if self.t.is_tensor(obj):
                    return obj.detach().cpu().clone()
                if isinstance(obj, dict):
                    return {k: cpu_copy(v) for k, v in obj.items()}
                if isinstance(obj, (tuple, list)):
                    return type(obj)(cpu_copy(v) for v in obj)
                return copy.deepcopy(obj)
            with self.model_lock:
                with self.save_lock:
                    memory = list(self.memory)
                    generation = max(self.generation, self.model_generation, checkpoint_generation or 0) + 1
                    protected_slot = self.model_slot if self.model_slot >= 0 else (checkpoint_slot if checkpoint_slot is not None and checkpoint_slot >= 0 else self.slot)
                    slot = (protected_slot + 1) % 2
                    model_slot = slot
                    steps = self.steps
                    snapshot = {'version': 12, 'generation': generation, 'q': cpu_copy(self.q.state_dict()), 'target': cpu_copy(self.target.state_dict()), 'opt': cpu_copy(self.optq.state_dict()), 'steps': steps, 'grads': self.grads, 'replay_count': len(memory)}
            path = self.folder / f'model.{model_slot}.pt'
            tmp = self.folder / f'model.{model_slot}.pt.tmp'
            try:
                with open(tmp, 'wb') as raw:
                    self.t.save(snapshot, raw)
                    raw.flush()
                    os.fsync(raw.fileno())
                save_replay(self.folder, memory, slot, generation)
                os.replace(tmp, path)
                with self.save_lock:
                    self.generation, self.slot = generation, slot
                    self.model_generation, self.model_slot = generation, model_slot
                discard_recovery(self.folder, generation)
            finally:
                if tmp.exists():
                    try:
                        tmp.unlink()
                    except OSError:
                        pass


def validate_network(torch, engine, device):
    model = copy.deepcopy(engine.q).to(device)
    target = copy.deepcopy(model).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=.00028)
    sample = bytes((i * 29) % 256 for i in range(VIS_N))
    frames = engine.images([sample, sample])
    meta = torch.tensor([[.1] * META_N, [-.1] * META_N], dtype=torch.float32, device=device)
    actions = torch.tensor([1, 4], dtype=torch.long, device=device)
    controls = torch.tensor([anchor_control(1), anchor_control(4)], dtype=torch.float32, device=device)
    for _ in range(2):
        model.train()
        logits, predicted, features = model(frames, meta)
        selected = logits.gather(1, actions.unsqueeze(1)).squeeze(1)
        movement = predicted.gather(1, actions[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
        observed = model.effect_value(features, controls)
        reliability = model.execute_value(features, controls)
        with torch.no_grad():
            online = model(frames, meta)[0]
            masked = torch.ones(ACT_N, dtype=torch.bool, device=device)
            masked[candidates({'l': False, 'r': False, 'm': False})] = False
            online[0].masked_fill_(masked, -1e8)
            best = online.argmax(dim=1, keepdim=True)
            future = target(frames, meta)[0].gather(1, best).squeeze(1)
            expected = torch.tensor([.01, -.02], dtype=torch.float32, device=device) + .975 * future
        predicted_features = model.next_features(features, controls)
        future_features = target(frames, meta)[2].detach()
        loss = torch.nn.functional.smooth_l1_loss(selected, expected) + .03 * (movement - controls).square().mean() + .2 * torch.nn.functional.smooth_l1_loss(observed, expected) + torch.nn.functional.smooth_l1_loss(reliability, torch.ones_like(reliability)) + torch.nn.functional.smooth_l1_loss(predicted_features, future_features)
        if not bool(torch.isfinite(loss).item()):
            raise ValueError('实际模型计算产生非法数值')
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.)
        optimizer.step()
    model.eval()
    with torch.no_grad():
        logits, predicted, features = model(frames, meta)
        if not bool(torch.isfinite(logits).all().item()) or not bool(torch.isfinite(predicted).all().item()) or not bool(torch.isfinite(model.effect_value(features, controls)).all().item()) or not bool(torch.isfinite(model.execute_value(features, controls)).all().item()) or not bool(torch.isfinite(model.next_features(features, controls)).all().item()):
            raise ValueError('实际模型推理产生非法数值')
    def cpu_copy(value):
        if torch.is_tensor(value):
            return value.detach().cpu()
        if isinstance(value, dict):
            return {key: cpu_copy(part) for key, part in value.items()}
        if isinstance(value, (list, tuple)):
            return type(value)(cpu_copy(part) for part in value)
        return value
    with torch.no_grad():
        for destination, source in zip(target.parameters(), model.parameters()):
            destination.lerp_(source, .04)
    stream = io.BytesIO()
    torch.save({'q': cpu_copy(model.state_dict()), 'opt': cpu_copy(optimizer.state_dict())}, stream)
    stream.seek(0)
    state = torch.load(stream, map_location='cpu', weights_only=True)
    model.load_state_dict(state['q'])
    if getattr(device, 'type', None) == 'cuda':
        torch.cuda.synchronize(device)
    del model, target, optimizer, frames, meta

def hardware_probe(backend, folder):
    try:
        torch = importlib.import_module('torch')
        if backend == 'cuda':
            devices = [torch.device('cuda:' + str(i)) for i in range(torch.cuda.device_count())]
        elif backend == 'directml':
            directml = importlib.import_module('torch_directml')
            devices = [directml.device(i) for i in range(directml.device_count())]
        else:
            return False
        passed = False
        for device in devices:
            try:
                engine = TorchBrain(Path(folder) / '.probe_readonly', torch, device, '检测')
                validate_network(torch, engine, device)
                if backend == 'cuda':
                    test = torch.randn(2048, 128, device=device)
                    output = (test @ test.transpose(0, 1)).mean()
                    torch.cuda.synchronize(device)
                    if not bool(torch.isfinite(output).item()):
                        raise RuntimeError('CUDA 矩阵计算自检失败')
                passed = True
                del engine
            except Exception as error:
                sys.stderr.write(str(device) + ' ' + type(error).__name__ + ': ' + str(error)[:160] + '\n')
        return passed
    except Exception as error:
        sys.stderr.write(type(error).__name__ + ': ' + str(error)[:160] + '\n')
    return False


def torch_engine_main(channel, folder_name, runtime_name, backend, cancel_event, preempt_event):
    try:
        if runtime_name:
            sys.path.insert(0, runtime_name)
        importlib.invalidate_caches()
        torch = importlib.import_module('torch')
        if backend == 'cuda':
            indices = list(range(torch.cuda.device_count()))
            def available_memory(index):
                try:
                    return torch.cuda.mem_get_info(index)[0]
                except Exception:
                    return 0
            indices.sort(key=available_memory, reverse=True)
            devices = [(torch.device('cuda:' + str(i)), 'GPU · ' + torch.cuda.get_device_name(i)) for i in indices]
        elif backend == 'directml':
            directml = importlib.import_module('torch_directml')
            devices = [(directml.device(i), 'GPU · DirectML · ' + (directml.device_name(i) if hasattr(directml, 'device_name') else str(i + 1))) for i in range(directml.device_count())]
        else:
            torch.set_num_threads(max(1, min(os.cpu_count() or 1, int(math.sqrt((os.cpu_count() or 1) * 2)))))
            devices = [(torch.device('cpu'), 'CPU · PyTorch')]
        engine = None
        diagnostics = []
        for device, title in devices:
            try:
                engine = TorchBrain(Path(folder_name), torch, device, title)
                validate_network(torch, engine, device)
                break
            except Exception as error:
                diagnostics.append(str(title) + '：' + str(error)[:160])
                engine = None
        if engine is None:
            raise RuntimeError('；'.join(diagnostics) or '没有通过计算验证的设备')
        channel.send(('ready', (engine.label, engine.steps, engine.generation, len(engine.memory))))
        save_thread = None
        save_error = []
        def run_checkpoint():
            try:
                engine.save()
            except BaseException as error:
                save_error.append(type(error).__name__ + ': ' + str(error)[:250])
        def await_checkpoint():
            nonlocal save_thread
            if save_thread is not None:
                save_thread.join()
                save_thread = None
            if save_error:
                raise RuntimeError(save_error.pop(0))
        while True:
            try:
                request_id, operation, payload = channel.recv()
            except EOFError:
                break
            try:
                if operation == 'choose':
                    result = engine.choose(*payload)
                elif operation == 'learn':
                    engine.learn(*payload)
                    result = None
                elif operation == 'train':
                    trained = engine.train(payload, AnyStop(cancel_event, preempt_event))
                    result = (trained, engine.performance())
                elif operation == 'begin_sleep':
                    engine.begin_sleep()
                    result = None
                elif operation == 'end_sleep':
                    result = engine.end_sleep()
                elif operation == 'sleep_progress':
                    result = engine.sleep_progress()
                elif operation == 'checkpoint_async':
                    if save_error:
                        raise RuntimeError(save_error.pop(0))
                    if save_thread is None or not save_thread.is_alive():
                        if save_thread is not None:
                            await_checkpoint()
                        save_thread = threading.Thread(target=run_checkpoint, daemon=False)
                        save_thread.start()
                    result = None
                elif operation == 'save':
                    await_checkpoint()
                    engine.save(*(payload or ()))
                    result = (engine.generation, engine.slot)
                elif operation == 'sync':
                    records, steps = payload
                    result = engine.restore_experience(records, steps)
                elif operation == 'mark_last_done':
                    with engine.save_lock:
                        if engine.memory:
                            last = engine.memory.pop()
                            engine.memory.append((*last[:6], True, *last[7:]))
                    result = None
                elif operation == 'close':
                    await_checkpoint()
                    channel.send(('ok', request_id, None))
                    break
                else:
                    raise ValueError('未识别的计算指令')
                channel.send(('ok', request_id, result))
            except Exception as error:
                channel.send(('error', request_id, type(error).__name__ + ': ' + str(error)[:320]))
    except BaseException as error:
        try:
            channel.send(('error', type(error).__name__ + ': ' + str(error)[:320]))
        except Exception:
            pass
    finally:
        channel.close()


class RemoteBrain:
    def __init__(self, folder, runtime, backend):
        self.folder = folder
        self.runtime = Path(runtime) if runtime is not None else None
        self.engine_backend = backend
        self.accelerated = backend != 'cpu'
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.steps = 0
        self.generation = 0
        self.latest_replay_generation = 0
        self.slot = -1
        self.save_lock = threading.RLock()
        self.checkpoint_lock = threading.Lock()
        self.rpc_lock = threading.RLock()
        self.inference_pending = threading.Event()
        self.recent_inference = time.monotonic()
        self.recent_inference_cost = .0
        self.latest_perf = {}
        self.sleeping = False
        self.closed = False
        self.failed = False
        self.sequence = 0
        ctx = mp.get_context('spawn')
        self.train_cancel = ctx.Event()
        self.train_preempt = ctx.Event()
        self.channel, endpoint = ctx.Pipe()
        self.process = ctx.Process(target=torch_engine_main, args=(endpoint, str(folder), str(runtime) if runtime is not None else None, backend, self.train_cancel, self.train_preempt), daemon=True)
        try:
            self.process.start()
            endpoint.close()
            kind, value = self._receive(100)
            if kind != 'ready':
                raise RuntimeError(str(value))
            self.label, self.steps, self.generation, count = value
            engine_generation = self.generation
            recovered = list(replay_sources(folder))
            if recovered:
                generation, slot, records = max(recovered, key=lambda item: (item[0], item[1] == 'recovery'))
                self.latest_replay_generation = generation
                self.memory = records
                self.steps = max(self.steps, len(records))
                if generation != engine_generation or len(records) != count:
                    self.sync(list(self.memory), self.steps)
            self.generation = engine_generation
            self.slot = next((slot for generation, slot, _ in recovered if generation == engine_generation), self.slot)
        except BaseException:
            self.close()
            raise

    def _receive(self, timeout):
        if not self.channel.poll(timeout):
            self.failed = True
            self.train_cancel.set()
            self.train_preempt.set()
            raise TimeoutError('计算进程响应超时；连接已废弃，防止旧回复错配')
        try:
            return self.channel.recv()
        except (EOFError, OSError) as error:
            self.failed = True
            raise RuntimeError('计算进程意外退出') from error

    def _request(self, operation, payload=None, timeout=35):
        with self.rpc_lock:
            if self.closed or self.failed or not self.process.is_alive():
                raise RuntimeError('计算进程不可用，需要重新启动后端')
            self.sequence += 1
            identifier = self.sequence
            try:
                self.channel.send((identifier, operation, payload))
                result = self._receive(timeout)
                if len(result) != 3 or result[1] != identifier:
                    self.failed = True
                    raise RuntimeError('计算进程响应编号不一致，连接已废弃')
                kind, _, value = result
                if kind != 'ok':
                    raise RuntimeError(str(value))
                return value
            except (BrokenPipeError, EOFError, OSError):
                self.failed = True
                raise RuntimeError('计算进程通信失效，需要重新启动后端')

    def choose(self, ob, meta, held):
        self.inference_pending.set()
        self.train_preempt.set()
        started = time.monotonic()
        try:
            return self._request('choose', (ob, meta, held), timeout=15)
        finally:
            elapsed = time.monotonic() - started
            self.recent_inference_cost += (elapsed - self.recent_inference_cost) / math.sqrt(1. + self.steps)
            self.recent_inference = time.monotonic()
            self.inference_pending.clear()
            self.train_preempt.clear()

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False):
        data = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved))
        self._request('learn', data, timeout=15)
        with self.save_lock:
            self.memory.append(data)
            self.steps += 1

    def train(self, count, stop):
        if stop.is_set() or self.train_cancel.is_set() or self.inference_pending.is_set() or self.train_preempt.is_set():
            return 0
        if not self.sleeping and time.monotonic() - self.recent_inference < max(self.recent_inference_cost * 2., .02):
            return 0
        if not self.rpc_lock.acquire(blocking=False):
            return 0
        try:
            if self.inference_pending.is_set() or self.train_preempt.is_set():
                return 0
            batches = min(max(1, int(count)), max(1, int(4 * math.sqrt(math.log2(2. + len(self.memory))))) if self.sleeping else 1)
            result, perf = self._request('train', batches, timeout=max(45., batches * 3.))
            self.latest_perf = perf
            return result
        finally:
            self.rpc_lock.release()

    def cancel_train(self):
        self.train_cancel.set()

    def reset_train_cancel(self):
        self.train_cancel.clear()

    def begin_sleep(self):
        self.train_cancel.clear()
        self._request('begin_sleep')
        self.sleeping = True

    def end_sleep(self):
        try:
            return self._request('end_sleep')
        finally:
            self.sleeping = False

    def sleep_progress(self):
        return self._request('sleep_progress')

    def mark_last_done(self):
        with self.save_lock:
            if self.memory:
                last = self.memory.pop()
                self.memory.append((*last[:6], True, *last[7:]))
        self._request('mark_last_done')

    def sync(self, records, steps):
        entries = list(records)[-REPLAY_LIMIT:]
        count = max(int(steps), len(entries))
        self._request('sync', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def checkpoint(self):
        if self.checkpoint_lock.acquire(blocking=False):
            try:
                self._request('checkpoint_async', timeout=10)
            finally:
                self.checkpoint_lock.release()

    def save(self):
        with self.checkpoint_lock:
            generation, slot = self._request('save', (max(self.generation, self.latest_replay_generation), self.slot), timeout=100)
            self.generation, self.latest_replay_generation, self.slot = generation, generation, slot

    def close(self):
        if self.closed:
            return
        self.closed = True
        self.sleeping = False
        self.train_cancel.set()
        self.train_preempt.set()
        try:
            if self.process.is_alive():
                try:
                    self.channel.send((self.sequence + 1, 'close', None))
                    self.channel.poll(2)
                except (OSError, EOFError):
                    pass
                self.process.join(timeout=2)
                if self.process.is_alive():
                    self.process.terminate()
                    self.process.join(timeout=2)
        finally:
            self.channel.close()
            try:
                self.process.close()
            except (OSError, ValueError):
                pass


if os.name == 'nt':
    from ctypes import wintypes
    u = ctypes.WinDLL('user32', use_last_error=True)
    g = ctypes.WinDLL('gdi32', use_last_error=True)

    class POINT(ctypes.Structure):
        _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

    class RECT(ctypes.Structure):
        _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long), ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

    class BITMAPINFOHEADER(ctypes.Structure):
        _fields_ = [('biSize', wintypes.DWORD), ('biWidth', ctypes.c_long), ('biHeight', ctypes.c_long), ('biPlanes', wintypes.WORD), ('biBitCount', wintypes.WORD), ('biCompression', wintypes.DWORD), ('biSizeImage', wintypes.DWORD), ('biXPelsPerMeter', ctypes.c_long), ('biYPelsPerMeter', ctypes.c_long), ('biClrUsed', wintypes.DWORD), ('biClrImportant', wintypes.DWORD)]

    class RGBQUAD(ctypes.Structure):
        _fields_ = [('b', ctypes.c_ubyte), ('g', ctypes.c_ubyte), ('r', ctypes.c_ubyte), ('a', ctypes.c_ubyte)]

    class BITMAPINFO(ctypes.Structure):
        _fields_ = [('bmiHeader', BITMAPINFOHEADER), ('bmiColors', RGBQUAD * 1)]

    WNDPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
    u.EnumWindows.argtypes = (WNDPROC, wintypes.LPARAM)
    u.IsWindowVisible.argtypes = (wintypes.HWND,)
    u.IsWindowVisible.restype = wintypes.BOOL
    u.IsIconic.argtypes = (wintypes.HWND,)
    u.GetWindowTextLengthW.argtypes = (wintypes.HWND,)
    u.GetWindowTextW.argtypes = (wintypes.HWND, wintypes.LPWSTR, ctypes.c_int)
    u.GetClientRect.argtypes = (wintypes.HWND, ctypes.POINTER(RECT))
    u.GetWindowRect.argtypes = (wintypes.HWND, ctypes.POINTER(RECT))
    u.ClientToScreen.argtypes = (wintypes.HWND, ctypes.POINTER(POINT))
    u.GetForegroundWindow.restype = wintypes.HWND
    u.SetForegroundWindow.argtypes = (wintypes.HWND,)
    u.ShowWindow.argtypes = (wintypes.HWND, ctypes.c_int)
    u.GetAncestor.argtypes = (wintypes.HWND, wintypes.UINT)
    u.GetAncestor.restype = wintypes.HWND
    u.IsWindow.argtypes = (wintypes.HWND,)
    u.IsWindow.restype = wintypes.BOOL
    u.GetClassNameW.argtypes = (wintypes.HWND, wintypes.LPWSTR, ctypes.c_int)
    u.GetWindowThreadProcessId.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.DWORD))
    u.GetWindowThreadProcessId.restype = wintypes.DWORD
    u.GetCursorPos.argtypes = (ctypes.POINTER(POINT),)
    u.SetCursorPos.argtypes = (ctypes.c_int, ctypes.c_int)
    u.SetCursorPos.restype = wintypes.BOOL
    u.WindowFromPoint.argtypes = (POINT,)
    u.WindowFromPoint.restype = wintypes.HWND
    u.GetAsyncKeyState.argtypes = (ctypes.c_int,)
    u.GetAsyncKeyState.restype = ctypes.c_short
    KBDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)
    MSPROC = KBDPROC

    class MSLLHOOKSTRUCT(ctypes.Structure):
        _fields_ = [('pt', POINT), ('mouseData', wintypes.DWORD), ('flags', wintypes.DWORD), ('time', wintypes.DWORD), ('extra', ctypes.c_size_t)]
    u.SetWindowsHookExW.argtypes = (ctypes.c_int, KBDPROC, wintypes.HINSTANCE, wintypes.DWORD)
    u.SetWindowsHookExW.restype = wintypes.HHOOK
    u.UnhookWindowsHookEx.argtypes = (wintypes.HHOOK,)
    u.CallNextHookEx.argtypes = (wintypes.HHOOK, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)
    u.CallNextHookEx.restype = ctypes.c_ssize_t
    u.GetMessageW.argtypes = (ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT)
    u.PeekMessageW.argtypes = (ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT, wintypes.UINT)
    u.PostThreadMessageW.argtypes = (wintypes.DWORD, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM)
    kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel32.GetCurrentThreadId.restype = wintypes.DWORD
    kernel32.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.QueryFullProcessImageNameW.argtypes = (wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD))
    kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL
    kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
    class MOUSEINPUT(ctypes.Structure):
        _fields_ = [('dx', ctypes.c_long), ('dy', ctypes.c_long), ('mouseData', wintypes.DWORD), ('dwFlags', wintypes.DWORD), ('time', wintypes.DWORD), ('dwExtraInfo', ctypes.c_size_t)]

    class KEYBDINPUT(ctypes.Structure):
        _fields_ = [('wVk', wintypes.WORD), ('wScan', wintypes.WORD), ('dwFlags', wintypes.DWORD), ('time', wintypes.DWORD), ('dwExtraInfo', ctypes.c_size_t)]

    class HARDWAREINPUT(ctypes.Structure):
        _fields_ = [('uMsg', wintypes.DWORD), ('wParamL', wintypes.WORD), ('wParamH', wintypes.WORD)]

    class INPUTUNION(ctypes.Union):
        _fields_ = [('mi', MOUSEINPUT), ('ki', KEYBDINPUT), ('hi', HARDWAREINPUT)]

    class INPUT(ctypes.Structure):
        _fields_ = [('type', wintypes.DWORD), ('data', INPUTUNION)]

    u.GetDoubleClickTime.restype = wintypes.UINT
    u.SendInput.argtypes = (wintypes.UINT, ctypes.POINTER(INPUT), ctypes.c_int)
    u.SendInput.restype = wintypes.UINT
    u.GetDC.argtypes = (wintypes.HWND,)
    u.GetDC.restype = wintypes.HDC
    u.ReleaseDC.argtypes = (wintypes.HWND, wintypes.HDC)
    g.CreateCompatibleDC.argtypes = (wintypes.HDC,)
    g.CreateCompatibleDC.restype = wintypes.HDC
    g.CreateDIBSection.argtypes = (wintypes.HDC, ctypes.POINTER(BITMAPINFO), wintypes.UINT, ctypes.POINTER(ctypes.c_void_p), wintypes.HANDLE, wintypes.DWORD)
    g.CreateDIBSection.restype = wintypes.HBITMAP
    g.SelectObject.argtypes = (wintypes.HDC, wintypes.HGDIOBJ)
    g.SelectObject.restype = wintypes.HGDIOBJ
    g.StretchBlt.argtypes = (wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.DWORD)
    g.StretchBlt.restype = wintypes.BOOL
    g.SetStretchBltMode.argtypes = (wintypes.HDC, ctypes.c_int)
    g.DeleteDC.argtypes = (wintypes.HDC,)
    g.DeleteObject.argtypes = (wintypes.HGDIOBJ,)
    try:
        ctypes.WinDLL('shcore').SetProcessDpiAwareness(2)
    except Exception:
        try:
            u.SetProcessDPIAware()
        except Exception:
            pass


def window_fingerprint(hwnd, title):
    identity = title.strip().casefold()
    if os.name != 'nt':
        return identity
    pid = wintypes.DWORD()
    if not u.GetWindowThreadProcessId(hwnd, ctypes.byref(pid)):
        return identity
    classname = ctypes.create_unicode_buffer(256)
    u.GetClassNameW(hwnd, classname, len(classname))
    process = kernel32.OpenProcess(0x1000, False, pid.value)
    if process:
        try:
            buf = ctypes.create_unicode_buffer(32768)
            size = wintypes.DWORD(len(buf))
            if kernel32.QueryFullProcessImageNameW(process, 0, buf, ctypes.byref(size)):
                return buf.value.casefold() + '|' + classname.value.casefold()
        finally:
            kernel32.CloseHandle(process)
    return (classname.value.casefold() + '|' + identity) if classname.value else identity


def send_mouse(flags, data=0):
    packet = INPUT()
    packet.type = 0
    packet.data.mi = MOUSEINPUT(0, 0, ctypes.c_uint32(data).value, flags, 0, 0)
    if u.SendInput(1, ctypes.byref(packet), ctypes.sizeof(INPUT)) != 1:
        raise OSError(ctypes.get_last_error(), '鼠标输入注入失败')


class WindowsIO:
    def __init__(self, hwnd):
        self.hwnd = int(hwnd)
        self.window_pid = wintypes.DWORD()
        u.GetWindowThreadProcessId(self.hwnd, ctypes.byref(self.window_pid))
        self.io_lock = threading.RLock()
        self.velocity = (0., 0.)
        self.grabber = None
        self.grabber_errors = 0
        self.wgc = None
        self.wgc_control = None
        self.wgc_lock = threading.Lock()
        self.wgc_frame = None
        self.wgc_stamp = 0.
        self.wgc_frame_id = 0
        self.last_frame_id = -1
        self.wgc_periods = deque(maxlen=96)
        self.post_action_capture = False
        self.last_capture_ms = 0.
        self.capture_epoch = 0
        self.last_frame_backend = None
        self.last_frame_valid = True
        self.last_capture_stamp = 0.
        self.capture_metadata = []
        try:
            dxcam = importlib.import_module('dxcam')
            self.grabber = dxcam.create(output_color='BGR')
        except (ImportError, OSError, RuntimeError, ValueError):
            pass
        self.src = u.GetDC(None)
        if not self.src:
            raise OSError('无法连接屏幕捕获设备')
        self.mem = g.CreateCompatibleDC(self.src)
        if not self.mem:
            u.ReleaseDC(None, self.src)
            raise OSError('无法创建图像缓冲区')
        self.ptr = ctypes.c_void_p()
        inf = BITMAPINFO()
        inf.bmiHeader.biSize = ctypes.sizeof(BITMAPINFOHEADER)
        inf.bmiHeader.biWidth = VIS_W
        inf.bmiHeader.biHeight = -VIS_H
        inf.bmiHeader.biPlanes = 1
        inf.bmiHeader.biBitCount = 32
        self.bmp = g.CreateDIBSection(self.src, ctypes.byref(inf), 0, ctypes.byref(self.ptr), None, 0)
        if not self.bmp or not self.ptr.value:
            g.DeleteDC(self.mem)
            u.ReleaseDC(None, self.src)
            raise OSError('无法创建窗口画面捕获资源')
        self.old = g.SelectObject(self.mem, self.bmp)
        g.SetStretchBltMode(self.mem, 3)
        self.down = {'l': False, 'r': False, 'm': False}
        self.hold_since = {}
        self.last_scroll = 0.0
        self.last_ai_cursor = None
        self.scroll_log = deque(maxlen=24)
        self.hold_history = deque(maxlen=96)
        self.automatic_moves = deque(maxlen=32)
        try:
            windows_capture = importlib.import_module('windows_capture')
            self.wgc = windows_capture.WindowsCapture(window_hwnd=self.hwnd, cursor_capture=False, draw_border=False, minimum_update_interval=40)
            @self.wgc.event
            def on_frame_arrived(frame, capture_control):
                with self.wgc_lock:
                    current = time.monotonic()
                    if self.wgc_stamp and current > self.wgc_stamp:
                        self.wgc_periods.append(current - self.wgc_stamp)
                    self.wgc_frame = frame.frame_buffer.copy()
                    self.wgc_stamp = current
                    self.wgc_frame_id += 1
            @self.wgc.event
            def on_closed():
                with self.wgc_lock:
                    self.wgc_frame = None
                    self.wgc_stamp = 0.
                    self.wgc_frame_id += 1
            self.wgc_control = self.wgc.start_free_threaded()
        except Exception:
            self.wgc = None
            self.wgc_control = None
        self.halted = threading.Event()

    @staticmethod
    def windows(except_hwnd):
        out = []
        def callback(hwnd, lparam):
            if int(hwnd) == except_hwnd or not u.IsWindowVisible(hwnd) or u.IsIconic(hwnd):
                return True
            length = u.GetWindowTextLengthW(hwnd)
            if length <= 0:
                return True
            buf = ctypes.create_unicode_buffer(length + 1)
            u.GetWindowTextW(hwnd, buf, length + 1)
            r = RECT()
            if u.GetClientRect(hwnd, ctypes.byref(r)) and r.right - r.left >= 80 and r.bottom - r.top >= 60:
                title = buf.value.strip()
                if title:
                    out.append((int(hwnd), title))
            return True
        func = WNDPROC(callback)
        u.EnumWindows(func, 0)
        return out

    def region(self):
        pid = wintypes.DWORD()
        if not u.IsWindow(self.hwnd) or u.IsIconic(self.hwnd) or not u.GetWindowThreadProcessId(self.hwnd, ctypes.byref(pid)) or pid.value != self.window_pid.value:
            return None
        rect = RECT()
        if not u.GetClientRect(self.hwnd, ctypes.byref(rect)):
            return None
        p = POINT(0, 0)
        if not u.ClientToScreen(self.hwnd, ctypes.byref(p)):
            return None
        w, h = rect.right - rect.left, rect.bottom - rect.top
        if w < 80 or h < 60:
            return None
        return (p.x, p.y, w, h)

    def foreground(self):
        return int(u.GetForegroundWindow() or 0) == self.hwnd and bool(u.IsWindow(self.hwnd)) and not bool(u.IsIconic(self.hwnd))

    def pointer_on_target(self, px, py):
        found = u.WindowFromPoint(POINT(px, py))
        if not found:
            return False
        return int(u.GetAncestor(found, 2) or found) == self.hwnd

    def activate(self):
        u.ShowWindow(self.hwnd, 9)
        u.SetForegroundWindow(self.hwnd)

    def cursor(self):
        p = POINT()
        u.GetCursorPos(ctypes.byref(p))
        return (p.x, p.y)

    def keys(self):
        return {k: bool(u.GetAsyncKeyState(v) & 0x8000) for k, v in (('l', 1), ('r', 2), ('m', 4))}

    def keyboard_activity(self):
        return any(u.GetAsyncKeyState(key) & 0x8000 for key in range(8, 255))

    def captured(self, content, backend, stamp, frame_id=None):
        self.capture_metadata.append((backend, stamp, frame_id))
        return content

    def capture(self, x, y, w, h):
        if self.wgc is not None:
            try:
                with self.wgc_lock:
                    image = self.wgc_frame
                    stamp = self.wgc_stamp
                    frame_id = self.wgc_frame_id
                if image is not None and time.monotonic() - stamp <= .35 and len(image.shape) == 3 and image.shape[2] >= 3:
                    bounds = RECT()
                    if u.GetWindowRect(self.hwnd, ctypes.byref(bounds)):
                        iw, ih = image.shape[1], image.shape[0]
                        ww, wh = bounds.right - bounds.left, bounds.bottom - bounds.top
                        if ww > 0 and wh > 0:
                            left = (x - bounds.left) * iw / ww
                            top = (y - bounds.top) * ih / wh
                            right = (x + w - bounds.left) * iw / ww
                            bottom = (y + h - bounds.top) * ih / wh
                            if left >= -1 and top >= -1 and right <= iw + 1 and bottom <= ih + 1:
                                import numpy as np
                                ys = np.clip(np.linspace(top, bottom - 1, VIS_H).astype(np.intp), 0, ih - 1)
                                xs = np.clip(np.linspace(left, right - 1, VIS_W).astype(np.intp), 0, iw - 1)
                                sample = image[ys[:, None], xs[None, :], :3]
                                return self.captured(sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes(), 'wgc', stamp, frame_id)
            except Exception:
                pass
        if self.grabber is not None and self.grabber_errors < max(3, int(math.sqrt(max(1, self.capture_epoch + 1)))):
            try:
                image = self.grabber.grab(region=(x, y, x + w, y + h), new_frame_only=self.post_action_capture and not self.capture_metadata)
                if image is not None and len(image.shape) == 3 and image.shape[2] >= 3:
                    import numpy as np
                    ys = np.linspace(0, image.shape[0] - 1, VIS_H).astype(np.intp)
                    xs = np.linspace(0, image.shape[1] - 1, VIS_W).astype(np.intp)
                    sample = image[ys[:, None], xs[None, :], :3]
                    self.grabber_errors = 0
                    return self.captured(sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes(), 'dxcam', time.monotonic())
            except Exception:
                self.grabber_errors += 1
        if not g.StretchBlt(self.mem, 0, 0, VIS_W, VIS_H, self.src, x, y, w, h, 0x00CC0020):
            raise OSError('画面获取失败')
        raw = ctypes.string_at(self.ptr, PIXELS * 4)
        return self.captured(raw[2::4] + raw[1::4] + raw[0::4], 'gdi', time.monotonic())

    def image(self, region):
        capture_start = time.monotonic()
        self.capture_metadata = []
        x, y, w, h = region
        overview = self.capture(x, y, w, h)
        px, py = self.cursor()
        zoom_w = max(48, min(w, int(w * .22)))
        zoom_h = max(32, min(h, int(h * .22)))
        crop_x = max(x, min(x + w - zoom_w, px - zoom_w // 2))
        crop_y = max(y, min(y + h - zoom_h, py - zoom_h // 2))
        result = overview + self.capture(crop_x, crop_y, zoom_w, zoom_h)
        captured_at = time.monotonic()
        modes = tuple(record[0] for record in self.capture_metadata)
        backend = modes[0] if len(modes) == 2 and modes[0] == modes[1] else 'mixed'
        ids = [record[2] for record in self.capture_metadata]
        self.last_frame_id = ids[0] if backend == 'wgc' and len(set(ids)) == 1 else -1
        self.last_frame_valid = backend != 'mixed' and len(result) == VIS_N and (backend != 'wgc' or self.last_frame_id >= 0)
        if backend != self.last_frame_backend:
            self.capture_epoch += 1
            self.last_frame_backend = backend
        self.last_capture_stamp = min((stamp for _, stamp, _ in self.capture_metadata), default=0.)
        if backend == 'wgc' and captured_at - self.last_capture_stamp > max(.35, (captured_at - capture_start) * 3.):
            self.last_frame_valid = False
        self.last_capture_ms = (captured_at - capture_start) * 1000
        return result

    def fresh_image(self, region, action_finished, expected_epoch, stop):
        with self.wgc_lock:
            recent = sorted(self.wgc_periods)
        period = recent[min(len(recent) - 1, int(len(recent) * .9))] if recent else max(.016, self.last_capture_ms / 1000.)
        grace = max(period * 4., self.last_capture_ms / 1000. * 3., .12)
        deadline = action_finished + min(.8, grace)
        self.post_action_capture = True
        try:
            while not stop.is_set():
                self.safe(region, stop)
                frame = self.image(region)
                if self.capture_epoch != expected_epoch:
                    return None
                if self.last_frame_valid and self.last_capture_stamp > action_finished:
                    return frame
                if time.monotonic() >= deadline:
                    return None
                if stop.wait(min(.02, max(0., deadline - time.monotonic()))):
                    raise InterruptedError('控制已停止')
            raise InterruptedError('控制已停止')
        finally:
            self.post_action_capture = False

    def safe(self, region, stop, require_pointer=True):
        if stop.is_set() or self.halted.is_set():
            raise InterruptedError('键盘急停')
        if not self.foreground() or self.region() != region:
            raise RuntimeError('窗口焦点或位置发生变化，控制已停止')
        if require_pointer:
            x, y, w, h = region
            px, py = self.cursor()
            if not (x + 3 <= px < x + w - 3 and y + 3 <= py < y + h - 3) or not self.pointer_on_target(px, py):
                raise RuntimeError('鼠标不在目标窗口内，已停止')

    def prepare_cursor(self, region, stop):
        with self.io_lock:
            self.safe(region, stop, False)
            x, y, w, h = region
            px, py = self.cursor()
            if not (x + 3 <= px < x + w - 3 and y + 3 <= py < y + h - 3) or not self.pointer_on_target(px, py):
                self.safe(region, stop, False)
                if not u.SetCursorPos(x + w // 2, y + h // 2):
                    raise RuntimeError('无法定位到目标窗口')
            self.safe(region, stop)
            self.last_ai_cursor = self.cursor()
            self.velocity = (0., 0.)

    def button(self, name, press, stop=None, region=None):
        with self.io_lock:
            if self.down[name] == press:
                return False
            if press:
                if region is None or stop is None:
                    raise RuntimeError('缺少点击安全状态')
                self.safe(region, stop)
            elif region is not None and stop is not None:
                self.safe(region, stop)
            flags = {'l': (2, 4), 'r': (8, 16), 'm': (32, 64)}
            if stop is not None and stop.is_set():
                raise InterruptedError('键盘急停')
            send_mouse(flags[name][0 if press else 1])
            self.down[name] = press
            if press:
                self.hold_since[name] = time.monotonic()
            else:
                started = self.hold_since.pop(name, None)
                if started is not None:
                    self.hold_history.append(max(0., time.monotonic() - started))
            return True

    def quick_release(self):
        with self.io_lock:
            failure = None
            for name, flag in (('l', 4), ('r', 16), ('m', 64)):
                if not self.down[name]:
                    continue
                try:
                    send_mouse(flag)
                    self.down[name] = False
                    started = self.hold_since.pop(name, None)
                    if started is not None:
                        self.hold_history.append(max(0., time.monotonic() - started))
                except OSError as error:
                    failure = error
            self.velocity = (0., 0.)
            if failure is not None:
                raise RuntimeError('AI 已按下的鼠标键释放未全部确认') from failure

    def release(self):
        self.quick_release()

    def halt(self):
        self.halted.set()
        self.quick_release()

    def act(self, ctrl, region, stop, dt):
        with self.io_lock:
            self.safe(region, stop)
            x, y, w, h = region
            px, py = self.cursor()
            movement_limit = max(3., math.sqrt(w * h) / max(1., math.sqrt(VIS_N)))
            if self.last_ai_cursor is not None and math.hypot(px - self.last_ai_cursor[0], py - self.last_ai_cursor[1]) > movement_limit:
                raise RuntimeError('检测到人工移动鼠标，AI 已停止')
            vx, vy, speed, l, r, m, wheel, duration = ctrl
            dt = max(.015, min(.25, float(dt)))
            speed_limit = speed_reference(region, dt)
            magnitude = max(.0, min(1., speed)) * speed_limit
            norm = math.hypot(vx, vy)
            ux, uy = ((vx / norm, vy / norm) if norm > .001 else (0., 0.))
            desired = (ux * magnitude, uy * magnitude)
            smooth = dt / (dt + max(dt / max(1., math.sqrt(max(1, w * h))), self.last_capture_ms / 1000.))
            velocity = (self.velocity[0] * (1 - smooth) + desired[0] * smooth, self.velocity[1] * (1 - smooth) + desired[1] * smooth)
            if not magnitude:
                velocity = (0., 0.)
            nx = max(x + 3, min(x + w - 4, round(px + velocity[0] * dt)))
            ny = max(y + 3, min(y + h - 4, round(py + velocity[1] * dt)))
            self.safe(region, stop)
            if stop.is_set():
                raise InterruptedError('键盘急停')
            if (nx, ny) != (px, py):
                self.automatic_moves.append((nx, ny, time.monotonic()))
                if not u.SetCursorPos(nx, ny):
                    raise RuntimeError('鼠标移动失败')
            self.safe(region, stop)
            ex, ey = self.cursor()
            dx, dy = ex - px, ey - py
            self.last_ai_cursor = (ex, ey)
            self.velocity = (dx / dt, dy / dt)
            switches = []
            blocked = False
            now = time.monotonic()
            observed_holds = sorted(self.hold_history)
            median_hold = observed_holds[len(observed_holds) // 2] if observed_holds else 0.
            hold_limit = max(u.GetDoubleClickTime() / 1000. * 4., median_hold * 3., dt * math.sqrt(max(1., w * h / PIXELS)))
            expired = set()
            for name, started in list(self.hold_since.items()):
                if self.down.get(name) and now - started > hold_limit:
                    if self.button(name, False, stop, region):
                        switches.append(name + '-')
                    expired.add(name)
                    blocked = True
            for name, target in zip(('l', 'r', 'm'), (l, r, m)):
                if name in expired:
                    continue
                if target > .5 and not self.down[name]:
                    if self.button(name, True, stop, region):
                        switches.append(name + '+')
                    else:
                        blocked = True
                elif target < -.5 and self.down[name]:
                    if self.button(name, False, stop, region):
                        switches.append(name + '-')
            delta = 0
            wheel = max(-1., min(1., wheel))
            if abs(wheel) > .08:
                while self.scroll_log and now - self.scroll_log[0] > 1.:
                    self.scroll_log.popleft()
                cadence = 1. / (1. + abs(wheel) * min(18., 1. / max(.015, dt)))
                scroll_limit = max(1, int(1. / max(.04, dt)))
                if now - self.last_scroll >= cadence and len(self.scroll_log) < scroll_limit:
                    self.safe(region, stop)
                    if stop.is_set():
                        raise InterruptedError('键盘急停')
                    delta = 120 if wheel > 0. else -120
                    send_mouse(0x0800, delta)
                    self.last_scroll = now
                    self.scroll_log.append(now)
            if switches:
                action = 17 + ('l+', 'l-', 'r+', 'r-', 'm+', 'm-').index(switches[0])
            elif delta:
                levels = sorted({abs(item[4]) for item in ACT if item[4]})
                threshold = sum(levels) / len(levels)
                action = (25 if delta > 0 else 26) if abs(wheel) > threshold else (23 if delta > 0 else 24)
            elif dx or dy:
                angle = math.atan2(dy, dx) % (2 * math.pi)
                sector = int(round(angle / (math.pi / 4))) % 8
                action = 1 + sector + (8 if math.hypot(dx, dy) / dt > speed_limit * .5 else 0)
            else:
                action = 0
            real_speed = min(1., math.hypot(dx, dy) / (dt * speed_limit))
            distance = math.hypot(dx, dy)
            executed = [dx / distance if distance else 0., dy / distance if distance else 0., real_speed, 0., 0., 0., math.copysign(abs(wheel), delta) if delta else 0., max(0., min(1., dt / .25))]
            for switch in switches:
                executed[{'l': 3, 'r': 4, 'm': 5}[switch[0]]] = 1. if switch[1] == '+' else -1.
            changed = bool(dx or dy or switches or delta)
            requested = bool(magnitude or delta or blocked or switches)
            intended_distance = magnitude * dt
            motion_fidelity = max(0., 1. - abs(distance - intended_distance) / max(1., intended_distance)) if intended_distance else 1.
            button_expected = [(name, target) for name, target in zip(('l', 'r', 'm'), (l, r, m)) if abs(target) > .5]
            button_fidelity = sum(self.down[name] == (target > .5) for name, target in button_expected) / len(button_expected) if button_expected else 1.
            wheel_fidelity = 1. if not abs(wheel) > .08 or delta or now - self.last_scroll < max(dt, 1. / (1. + abs(wheel) * min(18., 1. / max(.015, dt)))) else .5
            efficacy = max(0., min(1., motion_fidelity * button_fidelity * wheel_fidelity))
            return {'action': action, 'ctrl': tuple(executed), 'scroll': delta, 'switches': tuple(switches), 'blocked': blocked or (requested and not changed), 'changed': changed, 'moved': distance, 'efficacy': efficacy}

    def close(self):
        release_error = None
        try:
            self.release()
        except Exception as error:
            release_error = error
        if self.wgc_control is not None:
            try:
                self.wgc_control.stop()
            except Exception:
                pass
        if self.grabber is not None:
            try:
                self.grabber.stop()
                if hasattr(self.grabber, 'release'):
                    self.grabber.release()
            except (AttributeError, OSError, RuntimeError):
                pass
        if getattr(self, 'old', None):
            g.SelectObject(self.mem, self.old)
        if getattr(self, 'bmp', None):
            g.DeleteObject(self.bmp)
        if getattr(self, 'mem', None):
            g.DeleteDC(self.mem)
        if getattr(self, 'src', None):
            u.ReleaseDC(None, self.src)
        if release_error is not None:
            raise release_error


def detect_gpu():
    names = []
    if os.name == 'nt':
        try:
            class DISPLAY_DEVICE(ctypes.Structure):
                _fields_ = [('cb', wintypes.DWORD), ('DeviceName', ctypes.c_wchar * 32), ('DeviceString', ctypes.c_wchar * 128), ('StateFlags', wintypes.DWORD), ('DeviceID', ctypes.c_wchar * 128), ('DeviceKey', ctypes.c_wchar * 128)]
            display = u.EnumDisplayDevicesW
            display.argtypes = (wintypes.LPCWSTR, wintypes.DWORD, ctypes.POINTER(DISPLAY_DEVICE), wintypes.DWORD)
            for i in range(32):
                item = DISPLAY_DEVICE()
                item.cb = ctypes.sizeof(item)
                if not display(None, i, ctypes.byref(item), 0):
                    break
                name = item.DeviceString.strip()
                if name and name not in names and not any(x in name.lower() for x in ('basic display', 'remote display', 'mirror driver')):
                    names.append(name)
        except Exception:
            pass
        try:
            ctypes.WinDLL('nvcuda.dll')
            if not any('nvidia' in x.lower() for x in names):
                names.append('NVIDIA CUDA')
        except Exception:
            pass
        if not any('nvidia' in x.lower() for x in names):
            try:
                check = subprocess.run(['nvidia-smi', '-L'], text=True, capture_output=True, timeout=5, creationflags=subprocess.CREATE_NO_WINDOW)
                if check.returncode == 0 and 'GPU ' in check.stdout:
                    names.append('NVIDIA GPU')
            except (OSError, subprocess.SubprocessError):
                pass
    return names


def probe_acceleration(runtime, backend, folder, report=None, cancel=None):
    creation = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
    env = os.environ.copy()
    if runtime is not None:
        env['PYTHONPATH'] = str(runtime) + os.pathsep + env.get('PYTHONPATH', '')
    proc = None
    try:
        cmd = [sys.executable, str(Path(__file__).resolve()), '--mouseai-hardware-probe', backend, str(folder)]
        proc = subprocess.Popen(cmd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=creation)
        started = time.monotonic()
        while proc.poll() is None:
            if cancel is not None and cancel.is_set():
                proc.terminate()
                proc.communicate(timeout=5)
                return False
            if time.monotonic() - started > 100:
                proc.terminate()
                proc.communicate(timeout=5)
                if report is not None:
                    report(backend + ' 后端测试超时，已取消当前测试')
                return False
            time.sleep(.1)
        stdout, stderr = proc.communicate(timeout=5)
        passed = proc.returncode == 0 and 'READY' in stdout
        if not passed and report is not None:
            detail = (stderr or stdout).strip().splitlines()
            report(backend + ' 检测未通过' + ('：' + detail[-1][:180] if detail else ''))
        return passed
    except (OSError, subprocess.SubprocessError) as error:
        if report is not None:
            report(backend + ' 检测中断：' + str(error)[:150])
        return False
    finally:
        if proc is not None:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
            if proc.stdout is not None:
                proc.stdout.close()
            if proc.stderr is not None:
                proc.stderr.close()


def install_package(folder, args, report, cancel, backend):
    if cancel.is_set():
        return False
    folder.mkdir(parents=True, exist_ok=True)
    target = folder / ('.runtime_' + backend)
    staging = folder / ('.install_' + backend + '_' + os.urandom(6).hex())
    packages = staging / 'packages'
    temp = staging / 'tmp'
    packages.mkdir(parents=True, exist_ok=False)
    temp.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    for key in ('TMP', 'TEMP', 'TMPDIR', 'PIP_CACHE_DIR'):
        env[key] = str(temp)
    report('自动匹配并配置 ' + backend + ' 计算组件…')
    cmd = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', '--no-cache-dir', '--upgrade', '--target', str(packages)] + list(args)
    creation = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
    backup = folder / (target.name + '.backup')
    try:
        with open(staging / 'install.log', 'wb') as log:
            proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, creationflags=creation)
            started = time.monotonic()
            while proc.poll() is None:
                if cancel.is_set() or time.monotonic() - started > 600:
                    proc.terminate()
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait(timeout=5)
                    report(backend + ' 配置取消或超时，保留之前的计算组件')
                    return False
                time.sleep(.15)
        if proc.returncode != 0:
            lines = (staging / 'install.log').read_text(encoding='utf-8', errors='replace').strip().splitlines()
            report(backend + ' 安装失败' + ('：' + lines[-1][:180] if lines else ''))
            return False
        if backend.startswith('cuda_') and not probe_acceleration(packages, 'cuda', folder, report, cancel):
            return False
        if backend == 'directml' and not probe_acceleration(packages, 'directml', folder, report, cancel):
            return False
        if cancel.is_set():
            return False
        if backup.exists():
            shutil.rmtree(backup)
        if target.exists():
            os.replace(target, backup)
        try:
            os.replace(packages, target)
        except OSError:
            if backup.exists() and not target.exists():
                os.replace(backup, target)
            raise
        if backup.exists():
            shutil.rmtree(backup, ignore_errors=True)
        return True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report(backend + ' 配置异常：' + str(error)[:160])
        return False
    finally:
        shutil.rmtree(staging, ignore_errors=True)


def nvidia_driver_info():
    paths = ['nvidia-smi']
    if os.name == 'nt':
        program = os.environ.get('ProgramFiles', 'C:\\Program Files')
        paths.insert(0, str(Path(program) / 'NVIDIA Corporation' / 'NVSMI' / 'nvidia-smi.exe'))
        paths.insert(0, str(Path(os.environ.get('SystemRoot', 'C:/Windows')) / 'System32' / 'nvidia-smi.exe'))
    for binary in paths:
        try:
            completed = subprocess.run([binary, '--query-gpu=driver_version,name,memory.free', '--format=csv,noheader,nounits'], capture_output=True, text=True, timeout=7, creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
            if completed.returncode == 0 and completed.stdout.strip():
                return completed.stdout.strip().splitlines()
        except (OSError, subprocess.SubprocessError):
            pass
    return []


def cuda_driver_version():
    if os.name != 'nt':
        return None
    try:
        native = ctypes.WinDLL('nvcuda.dll')
        native.cuInit.argtypes = (ctypes.c_uint,)
        native.cuInit.restype = ctypes.c_int
        native.cuDriverGetVersion.argtypes = (ctypes.POINTER(ctypes.c_int),)
        native.cuDriverGetVersion.restype = ctypes.c_int
        if native.cuInit(0) == 0:
            version = ctypes.c_int()
            if native.cuDriverGetVersion(ctypes.byref(version)) == 0 and version.value > 0:
                return version.value // 1000, version.value % 1000 // 10
    except (OSError, AttributeError, ValueError):
        return None
    return None


def available_cuda_wheels(driver):
    try:
        with urllib.request.urlopen('https://download.pytorch.org/whl/', timeout=9) as response:
            listing = response.read(1000000).decode('utf-8', errors='replace')
        versions = sorted(set('cu' + value for value in re.findall(r'(?i)href=["\'][^"\']*cu(\d{3,4})/?["\']', listing)), key=lambda value: int(value[2:]), reverse=True)
    except (OSError, ValueError, TimeoutError):
        return []
    def compatible(wheel):
        if driver is None:
            return True
        digits = wheel[2:]
        major = int(digits[:-2]) if len(digits) == 4 else int(digits[:-1])
        minor = int(digits[-2:]) if len(digits) == 4 else int(digits[-1])
        return (major, minor) <= driver
    versions = [wheel for wheel in versions if compatible(wheel)]
    tag = 'cp' + str(sys.version_info.major) + str(sys.version_info.minor)
    supported = []
    for wheel in versions:
        try:
            with urllib.request.urlopen('https://download.pytorch.org/whl/' + wheel + '/torch/', timeout=8) as response:
                listing = response.read(16000000).decode('utf-8', errors='replace').lower()
            if tag in listing and 'win_amd64' in listing:
                supported.append(wheel)
        except (OSError, ValueError, TimeoutError):
            continue
    return supported


def load_brain(folder, report, cancel, runtime_folder=None):
    folder.mkdir(parents=True, exist_ok=True)
    runtime_folder = Path(runtime_folder) if runtime_folder is not None else folder
    runtime_folder.mkdir(parents=True, exist_ok=True)
    cache = runtime_folder / '.cache'
    cache.mkdir(parents=True, exist_ok=True)
    for key in ('TEMP', 'TMP', 'TMPDIR', 'XDG_CACHE_HOME', 'TORCH_HOME', 'CUDA_CACHE_PATH', 'TORCHINDUCTOR_CACHE_DIR', 'TRITON_CACHE_DIR'):
        os.environ[key] = str(cache)
    gpus = detect_gpu()
    nvidia = any('nvidia' in name.lower() for name in gpus)
    if gpus:
        report('识别的图形设备：' + '、'.join(gpus[:4]))
    if os.name == 'nt' and not nvidia and nvidia_driver_info():
        nvidia = True
        gpus.append('NVIDIA GPU')
    cuda_runtimes = sorted(runtime_folder.glob('.runtime_cuda_cu*'), reverse=True)
    directml_runtime = runtime_folder / '.runtime_directml'
    cpu_runtime = runtime_folder / '.runtime_cpu'
    if os.name == 'nt' and not cancel.is_set():
        tried = set()
        def launch(runtime, backend):
            key = (str(runtime) if runtime is not None else '', backend)
            if key in tried or cancel.is_set():
                return None
            tried.add(key)
            if not probe_acceleration(runtime, backend, folder, report, cancel):
                return None
            try:
                return RemoteBrain(folder, runtime, backend)
            except Exception as error:
                report(backend + ' 计算引擎启动失败：' + str(error)[:120])
                return None
        for runtime in [*cuda_runtimes, None]:
            ready = launch(runtime, 'cuda')
            if ready is not None:
                return ready
        if nvidia and not cancel.is_set():
            report('已识别 NVIDIA 显卡，正在确认驱动支持情况及匹配 CUDA 计算组件…')
            driver = cuda_driver_version()
            info = nvidia_driver_info()
            if info:
                report('NVIDIA 硬件诊断：' + '；'.join(info[:2])[:180])
            if driver is None:
                candidates_smi = ['nvidia-smi']
                candidates_smi.extend((str(Path(os.environ.get('SystemRoot', 'C:/Windows')) / 'System32' / 'nvidia-smi.exe'), str(Path(os.environ.get('ProgramFiles', 'C:/Program Files')) / 'NVIDIA Corporation' / 'NVSMI' / 'nvidia-smi.exe')))
                for binary in candidates_smi:
                    try:
                        result = subprocess.run([binary], text=True, capture_output=True, timeout=9, creationflags=subprocess.CREATE_NO_WINDOW)
                        match = re.search(r'CUDA Version:\s*(\d+)\.(\d+)', result.stdout)
                        if match:
                            driver = (int(match.group(1)), int(match.group(2)))
                            break
                    except (OSError, subprocess.SubprocessError):
                        continue
            wheels = available_cuda_wheels(driver)
            if driver is not None:
                report('NVIDIA 驱动报告支持 CUDA ' + '.'.join(map(str, driver)) + '；开始真实矩阵计算与训练验证')
            if not wheels:
                report('NVIDIA 驱动已检查，但未找到适配当前 Python/驱动的 CUDA Windows 安装包，或无法访问下载源；随后尝试 DirectML')
            for wheel in wheels:
                if cancel.is_set():
                    break
                runtime = runtime_folder / ('.runtime_cuda_' + wheel)
                if runtime.exists() and (runtime / 'torch').exists():
                    ready = launch(runtime, 'cuda')
                    if ready is not None:
                        return ready
                    continue
                if install_package(runtime_folder, ['--only-binary=:all:', '--index-url', 'https://download.pytorch.org/whl/' + wheel, 'torch'], report, cancel, 'cuda_' + wheel):
                    ready = launch(runtime, 'cuda')
                    if ready is not None:
                        return ready
        for runtime in ([directml_runtime, None] if directml_runtime.exists() else [None]):
            ready = launch(runtime, 'directml')
            if ready is not None:
                return ready
        if gpus and not cancel.is_set() and not (directml_runtime / 'torch_directml').exists():
            if install_package(runtime_folder, ['torch-directml'], report, cancel, 'directml'):
                ready = launch(directml_runtime, 'directml')
                if ready is not None:
                    return ready
    if cancel.is_set():
        return LiteBrain(folder)
    for runtime in (cpu_runtime if (cpu_runtime / 'torch').exists() else None,):
        try:
            return RemoteBrain(folder, runtime, 'cpu')
        except Exception as error:
            report('PyTorch CPU 后端初始化失败：' + str(error)[:120])
    if gpus:
        report('显卡 ' + '、'.join(gpus[:3]) + ' 的 CUDA/DirectML 计算验证未通过；当前采用 CPU，保留 GPU 运行时供后续重试')
    return LiteBrain(folder)

def ensure_capture(folder, report, cancel):
    if os.name != 'nt' or cancel.is_set():
        return
    try:
        importlib.import_module('windows_capture')
        return
    except (ImportError, OSError, RuntimeError):
        pass
    runtime = folder / '.runtime_capture'
    if str(runtime) not in sys.path:
        sys.path.insert(0, str(runtime))
    importlib.invalidate_caches()
    try:
        importlib.import_module('windows_capture')
        return
    except (ImportError, OSError, RuntimeError):
        pass
    marker = folder / '.capture_attempt'
    try:
        if marker.exists() and time.time() - marker.stat().st_mtime < 86400:
            return
        marker.touch()
        if not install_package(folder, ['windows-capture'], report, cancel, 'capture'):
            return
        importlib.invalidate_caches()
        importlib.import_module('windows_capture')
    except (OSError, ImportError, RuntimeError, ValueError):
        return


class MouseAIApp:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title('窗口鼠标 AI')
        self.root.configure(bg='#10131a')
        self.root.geometry('800x525')
        self.root.minsize(590, 430)
        home = Path.home()
        self.folder = (home / 'Documents' / 'MouseAI') if (home / 'Documents').exists() else (home / 'MouseAI')
        self.control_stop = threading.Event()
        self.online_stop = threading.Event()
        self.online_worker = None
        self.online_error = None
        self.active_io = None
        self.sleep_stop = threading.Event()
        self.exit_stop = threading.Event()
        self.worker = None
        self.key_thread_id = None
        self.wheel_lock = threading.Lock()
        self.wheel_events = deque(maxlen=128)
        self.wheel_hook_ready = False
        self.mouse_monitor_armed = threading.Event()
        self.backend_recovering = threading.Event()
        self.keyboard_ready = threading.Event()
        self.control_heartbeat = 0.
        self.watchdog_limit = 3.
        self.close_started = 0.
        self.saver = None
        self.exit_backup = None
        self.exit_backup_error = None
        self.last_checkpoint_step = 0
        self.control_history = deque(maxlen=max(4, int(math.sqrt(REPLAY_LIMIT))))
        self.next_backend_retry = 0.
        self.backend_faults = {}
        self.brain = None
        self.brain_folder = None
        self.mode = 'idle'
        self.message = queue.Queue()
        self.listing = {}
        self.iterations = 0
        self.backend = tk.StringVar(value='未启动')
        self.folder_text = tk.StringVar(value=str(self.folder))
        self.status = tk.StringVar(value='选择窗口后点击绿色按钮')
        self.statistics = tk.StringVar(value='经历 0 帧 · 睡眠训练 0 步')
        self.control_details = tk.StringVar(value='方向 (0, 0) · 速率 0 · 左/右/中键 已释放 · 滚轮 0')
        self.combo_var = tk.StringVar()
        self.environment_code = (0., 0.)
        self.data_folder = self.folder
        self.audit_sum = 0.
        self.audit_samples = 0
        self.build()
        self.root.protocol('WM_DELETE_WINDOW', self.close)
        self.root.after(90, self.pump)
        self.refresh_after = None
        self.refresh_after = self.root.after(400, self.refresh)
        self.key_thread = threading.Thread(target=self.keyboard_sentinel, daemon=True)
        self.key_thread.start()
        self.safety_thread = threading.Thread(target=self.safety_sentinel, daemon=True)
        self.safety_thread.start()

    def build(self):
        sty = ttk.Style(self.root)
        try:
            sty.theme_use('clam')
        except Exception:
            pass
        sty.configure('AI.TCombobox', font=('Microsoft YaHei UI', 11), padding=7)
        tk.Label(self.root, text='窗口鼠标 AI', bg='#10131a', fg='#f2f5fa', font=('Microsoft YaHei UI', 23, 'bold')).pack(anchor='w', padx=26, pady=(24, 4))
        tk.Label(self.root, text='双尺度视觉 · 有界鼠标控制 · 睡眠训练 · 自动模型回滚', bg='#10131a', fg='#8c99ad', font=('Microsoft YaHei UI', 10)).pack(anchor='w', padx=28, pady=(0, 18))
        tk.Label(self.root, text='目标窗口', bg='#10131a', fg='#d9e0ea', font=('Microsoft YaHei UI', 11)).pack(anchor='w', padx=28)
        section = tk.Frame(self.root, bg='#10131a')
        section.pack(fill='x', padx=26, pady=(8, 17))
        self.combo = ttk.Combobox(section, textvariable=self.combo_var, state='readonly', style='AI.TCombobox', font=('Microsoft YaHei UI', 10))
        self.combo.pack(side='left', fill='x', expand=True, ipady=3)
        tk.Button(section, text='刷新', command=self.refresh, bg='#303949', fg='white', relief='flat', cursor='hand2', font=('Microsoft YaHei UI', 10), padx=13, pady=8).pack(side='left', padx=(10, 0))
        buttons = tk.Frame(self.root, bg='#10131a')
        buttons.pack(fill='x', padx=26, pady=(0, 18))
        for text, color, command in [('●  开始控制', '#18ad65', self.start), ('●  睡觉学习', '#262933', self.sleep), ('●  提前唤醒', '#f1f4f8', self.wake), ('●  退出', '#dc454e', self.close)]:
            front = '#19222d' if color == '#f1f4f8' else '#ffffff'
            b = tk.Button(buttons, text=text, command=command, bg=color, fg=front, activebackground=color, activeforeground=front, font=('Microsoft YaHei UI', 10, 'bold'), relief='flat', bd=0, padx=8, pady=13, cursor='hand2')
            b.pack(side='left', fill='x', expand=True, padx=4)
        bar = tk.Frame(self.root, bg='#202631', padx=14, pady=12)
        bar.pack(fill='x', padx=26)
        tk.Label(bar, textvariable=self.status, bg='#202631', fg='#e0e8f2', wraplength=585, font=('Microsoft YaHei UI', 10)).pack(anchor='w')
        tk.Label(bar, textvariable=self.statistics, bg='#202631', fg='#91a0b8', font=('Microsoft YaHei UI', 9)).pack(anchor='w', pady=(8, 0))
        tk.Label(bar, textvariable=self.backend, bg='#202631', fg='#69cfbd', wraplength=585, font=('Microsoft YaHei UI', 9)).pack(anchor='w', pady=(6, 0))
        tk.Label(bar, textvariable=self.control_details, bg='#202631', fg='#bad0f0', wraplength=640, font=('Microsoft YaHei UI', 9)).pack(anchor='w', pady=(5, 0))
        bottom = tk.Frame(self.root, bg='#10131a')
        bottom.pack(fill='x', padx=26, pady=(18, 4))
        tk.Button(bottom, text='选择数据文件夹', command=self.choose_folder, bg='#303949', fg='#f5f7fa', relief='flat', padx=12, pady=7, cursor='hand2').pack(side='left')
        tk.Label(bottom, textvariable=self.folder_text, bg='#10131a', fg='#8793a7', anchor='w', font=('Microsoft YaHei UI', 9)).pack(side='left', fill='x', expand=True, padx=(10, 0))
        tk.Label(self.root, text='按下任意键盘按键可立即终止鼠标控制', bg='#10131a', fg='#ffbb85', font=('Microsoft YaHei UI', 10)).pack(anchor='w', padx=28, pady=(11, 10))

    def post(self, kind, value):
        self.message.put((kind, value))

    def pump(self):
        latest_control = None
        while True:
            try:
                kind, val = self.message.get_nowait()
            except queue.Empty:
                break
            if kind == 'status':
                self.status.set(val)
            elif kind == 'backend':
                self.backend.set(val)
            elif kind == 'stats':
                self.statistics.set(val)
            elif kind == 'control':
                latest_control = val
            elif kind == 'done':
                if self.mode != 'closed' and val == self.mode:
                    self.mode = 'idle'
            elif kind == 'error':
                self.status.set('发生问题：' + val)
        if latest_control is not None:
            self.control_details.set(latest_control)
        if self.mode == 'control' and (not self.keyboard_ready.is_set() or not self.wheel_hook_ready):
            self.emergency_stop('输入安全钩子不可用，已停止鼠标控制')
        if not self.exit_stop.is_set():
            self.root.after(90, self.pump)

    def refresh(self):
        if self.refresh_after is not None:
            try:
                self.root.after_cancel(self.refresh_after)
            except tk.TclError:
                pass
            self.refresh_after = None
        if os.name != 'nt':
            self.status.set('当前版本需要 Windows 11 x64')
            return
        try:
            root_hwnd = int(u.GetAncestor(self.root.winfo_id(), 2) or self.root.winfo_id())
            windows = WindowsIO.windows(root_hwnd)
            current = self.combo_var.get()
            self.listing = {f'{name[:76]}  [0x{hwnd:X}]': hwnd for hwnd, name in windows}
            vals = list(self.listing)
            self.combo['values'] = vals
            self.combo_var.set(current if current in self.listing else '')
        except Exception as ex:
            self.status.set('无法列举窗口：' + str(ex)[:90])
        if self.mode != 'closed' and not self.exit_stop.is_set():
            self.refresh_after = self.root.after(3000, self.refresh)

    def choose_folder(self):
        if self.mode != 'idle':
            self.status.set('请先停止运行后再更换数据文件夹')
            return
        new = filedialog.askdirectory(parent=self.root, initialdir=str(self.folder), title='选择 AI 数据存放文件夹')
        if new:
            folder = Path(new)
            if folder == self.folder:
                return
            if (self.worker is not None and self.worker.is_alive()) or (self.online_worker is not None and self.online_worker.is_alive()):
                self.status.set('运行线程尚未退出，暂不可更换文件夹')
                return
            if self.saver is not None and self.saver.is_alive():
                self.saver.join(timeout=8)
                if self.saver.is_alive():
                    self.status.set('正在保存之前的经验，请稍后重新选择')
                    return
            previous = self.brain
            if previous is not None:
                try:
                    previous.save()
                    if isinstance(previous, RemoteBrain):
                        previous.close()
                except Exception as ex:
                    self.status.set('原数据保存未完成：' + str(ex)[:95])
                    return
            self.brain = None
            self.brain_folder = None
            self.folder = folder
            self.folder_text.set(str(self.folder))
            self.backend.set('未启动')
            self.next_backend_retry = 0.
            self.backend_faults = {}
            self.data_folder = folder
            self.audit_sum = 0.
            self.audit_samples = 0
            self.status.set('已切换学习数据文件夹；旧计算资源已释放')

    def load(self, task_stop):
        if self.brain is not None and self.brain_folder != self.data_folder:
            self.brain.save()
            if isinstance(self.brain, RemoteBrain):
                self.brain.close()
            self.brain = None
            self.brain_folder = None
        if self.brain is not None and self.brain_folder == self.data_folder:
            retry = time.monotonic() >= self.next_backend_retry and bool(detect_gpu()) and not self.brain.accelerated
            if not retry:
                return
            self.post('status', '正在重新检查显卡驱动与计算后端…')
            self.brain.save()
        cancel = AnyStop(self.exit_stop, task_stop)
        if cancel.is_set():
            return
        self.post('status', '检测硬件并准备学习模型…')
        brain = load_brain(self.data_folder, lambda msg: self.post('status', msg), cancel, runtime_folder=self.folder)
        ensure_capture(self.folder, lambda msg: self.post('status', msg), cancel)
        if cancel.is_set():
            if isinstance(brain, RemoteBrain):
                brain.close()
            return
        previous_brain = self.brain
        if previous_brain is not None and brain is not previous_brain and self.brain_folder == self.data_folder:
            try:
                with previous_brain.save_lock:
                    old_rows = list(previous_brain.memory)
                    old_steps = previous_brain.steps
                    old_generation = previous_brain.generation
                with brain.save_lock:
                    new_rows = list(brain.memory)
                    new_steps = brain.steps
                    new_generation = brain.generation
                if old_generation > new_generation or (old_generation == new_generation and len(old_rows) > len(new_rows)):
                    if isinstance(brain, RemoteBrain):
                        brain.sync(old_rows, max(old_steps, new_steps))
                    else:
                        brain.restore_experience(old_rows, max(old_steps, new_steps))
                elif old_generation == new_generation and old_steps > new_steps:
                    if isinstance(brain, RemoteBrain):
                        brain.sync(new_rows, old_steps)
                    else:
                        brain.steps = old_steps
            except Exception:
                if isinstance(brain, RemoteBrain):
                    brain.close()
                raise
        self.brain = brain
        self.brain_folder = self.data_folder
        if previous_brain is not brain and isinstance(previous_brain, RemoteBrain):
            previous_brain.close()
        self.next_backend_retry = time.monotonic() + max(2., min(600., math.sqrt(max(1, brain.steps)))) if not brain.accelerated else 0.
        self.post('backend', self.brain.label)

    def recover_learning_backend(self, error):
        self.backend_recovering.set()
        self.mouse_monitor_armed.clear()
        try:
            active = self.active_io
            if active is not None:
                active.quick_release()
            self.online_stop.set()
            if self.online_worker is not None and self.online_worker.is_alive() and self.online_worker is not threading.current_thread():
                self.online_worker.join(timeout=5)
                if self.online_worker.is_alive():
                    raise RuntimeError('在线训练未能安全结束，已终止鼠标控制')
            if self.saver is not None and self.saver.is_alive():
                self.saver.join(timeout=8)
                if self.saver.is_alive():
                    raise RuntimeError('模型保存仍在运行，已终止鼠标控制')
            former = self.brain
            if former is None:
                raise RuntimeError('没有可恢复的学习模型')
            with former.save_lock:
                recovered = list(former.memory)
                steps = former.steps
            failures = self.backend_faults
            runtime_folder = self.folder
            choices = []
            if isinstance(former, RemoteBrain):
                faulty = (former.engine_backend, str(former.runtime) if former.runtime else '')
                failures[faulty] = (failures.get(faulty, (0, 0.))[0] + 1, time.monotonic())
                if former.engine_backend != 'cpu':
                    choices.append((former.engine_backend, former.runtime))
                try:
                    former.close()
                except (OSError, RuntimeError, ValueError) as close_error:
                    self.post('status', '旧计算进程关闭异常：' + str(close_error)[:85])
            else:
                faulty = None
            choices.extend(('cuda', path) for path in sorted(runtime_folder.glob('.runtime_cuda_cu*'), reverse=True) if (path / 'torch').is_dir())
            choices.append(('cuda', None))
            directml = runtime_folder / '.runtime_directml'
            if (directml / 'torch_directml').exists():
                choices.append(('directml', directml))
            choices.append(('directml', None))
            cpu = runtime_folder / '.runtime_cpu'
            choices.extend([('cpu', cpu if (cpu / 'torch').exists() else None), ('cpu', None)])
            seen = set()
            backup = None
            failures_seen = []
            self.post('status', '计算后端异常，先尝试恢复 GPU：' + str(error)[:75])
            for backend, runtime in choices:
                if self.exit_stop.is_set() or self.control_stop.is_set() or self.sleep_stop.is_set():
                    break
                key = (backend, str(runtime) if runtime else '')
                if key in seen:
                    continue
                seen.add(key)
                attempts, previous = failures.get(key, (0, 0.))
                backoff = min(600., math.pow(2., min(attempts, 9)))
                if attempts > 0 and not (key == faulty and attempts == 1) and time.monotonic() - previous < backoff:
                    continue
                if backend != 'cpu' and not probe_acceleration(runtime, backend, self.data_folder, lambda text: self.post('status', text), AnyStop(self.exit_stop, self.control_stop, self.sleep_stop)):
                    failures[key] = (attempts + 1, time.monotonic())
                    continue
                candidate = None
                try:
                    candidate = RemoteBrain(self.data_folder, runtime, backend)
                    if recovered:
                        candidate.sync(recovered, steps)
                    backup = candidate
                    failures.pop(key, None)
                    break
                except Exception as issue:
                    if candidate is not None:
                        try:
                            candidate.close()
                        except Exception:
                            pass
                    failures[key] = (attempts + 1, time.monotonic())
                    failures_seen.append(backend + '：' + str(issue)[:85])
            if backup is None:
                backup = LiteBrain(self.data_folder)
                backup.restore_experience(recovered, steps)
                if failures_seen:
                    self.post('status', '所有可用计算后端恢复失败：' + '；'.join(failures_seen[:3]))
            self.brain = backup
            self.brain_folder = self.data_folder
            self.next_backend_retry = time.monotonic() + max(2., min(600., math.sqrt(max(1, steps)))) if not backup.accelerated else 0.
            self.post('backend', backup.label)
        finally:
            self.backend_recovering.clear()

    def emergency_stop(self, reason):
        self.control_stop.set()
        self.mouse_monitor_armed.clear()
        self.control_heartbeat = 0.
        self.online_stop.set()
        if isinstance(self.brain, RemoteBrain):
            self.brain.cancel_train()
        active = self.active_io
        unreleased = False
        if active is not None:
            try:
                active.halt()
                unreleased = any(active.down.values())
            except Exception:
                unreleased = True
        if unreleased:
            self.post('error', '鼠标释放未获确认，正在尝试重试；可通过物理鼠标操作解除按住状态')
        elif reason:
            self.post('status', reason)

    def online_job(self, brain):
        while not self.online_stop.wait(.15) and not self.exit_stop.is_set() and not self.control_stop.is_set():
            if self.brain is not brain:
                return
            try:
                with brain.save_lock:
                    train_count = sum(not row[12] for row in brain.memory)
                if train_count >= max(8, int(math.sqrt(REPLAY_LIMIT))):
                    brain.train(1, self.online_stop)
            except Exception as ex:
                self.online_error = ex
                self.online_stop.set()
                return

    def start_online(self):
        if isinstance(self.brain, RemoteBrain):
            self.online_error = None
            self.online_stop.clear()
            self.brain.reset_train_cancel()
            self.online_worker = threading.Thread(target=self.online_job, args=(self.brain,), daemon=True)
            self.online_worker.start()

    def start(self):
        if os.name != 'nt' or struct.calcsize('P') != 8:
            self.status.set('需要 Windows 11 x64 与 64 位 Python 运行环境')
            return
        if not self.keyboard_ready.wait(.3):
            self.status.set('键盘与鼠标安全钩子未就绪，已阻止控制启动')
            return
        if self.mode != 'idle' or (self.worker is not None and self.worker.is_alive()):
            self.status.set('上一个操作尚未结束')
            return
        if (self.online_worker is not None and self.online_worker.is_alive()) or (self.saver is not None and self.saver.is_alive()):
            self.status.set('后台学习或数据保存尚未完成，暂不能重新开始控制')
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None:
            self.status.set('请先选择一个有效窗口')
            return
        descriptor = self.combo_var.get().rsplit('  [0x', 1)[0].strip().casefold()
        descriptor = window_fingerprint(hwnd, descriptor)
        identifier = hashlib.sha256(descriptor.encode('utf-8')).digest()
        self.environment_code = tuple((int.from_bytes(identifier[i:i + 4], 'little') / 4294967295.) * 2. - 1. for i in (0, 4))
        self.data_folder = self.folder / 'environments' / identifier.hex()[:24]
        self.control_stop.clear()
        self.backend_recovering.clear()
        self.mouse_monitor_armed.clear()
        self.mode = 'control'
        self.worker = threading.Thread(target=self.control_job, args=(hwnd,), daemon=True)
        self.worker.start()

    def wheel_delta(self):
        with self.wheel_lock:
            value = sum(self.wheel_events)
            self.wheel_events.clear()
        return value

    def safety_sentinel(self):
        canceled = False
        while not self.exit_stop.wait(.012):
            active = self.active_io
            if self.mode == 'control' and not self.control_stop.is_set():
                if not self.keyboard_ready.is_set() or not self.wheel_hook_ready or (active is not None and active.keyboard_activity()):
                    self.control_stop.set()
                    self.online_stop.set()
                    self.post('status', '检测到键盘输入或安全监控异常，已停止鼠标控制')
                elif not self.backend_recovering.is_set() and self.mouse_monitor_armed.is_set() and self.control_heartbeat > 0 and time.monotonic() - self.control_heartbeat > self.watchdog_limit:
                    self.control_stop.set()
                    self.mouse_monitor_armed.clear()
                    self.online_stop.set()
                    self.post('status', '控制计算长时间无响应，安全监控已停止并释放鼠标')
            if self.control_stop.is_set():
                if not canceled and isinstance(self.brain, RemoteBrain):
                    self.brain.cancel_train()
                canceled = True
                if active is not None and any(active.down.values()):
                    try:
                        active.halt()
                    except Exception:
                        pass
            else:
                canceled = False
        active = self.active_io
        if active is not None:
            try:
                active.halt()
            except Exception:
                pass

    def keyboard_sentinel(self):
        if os.name != 'nt':
            return
        key_hook = None
        mouse_hook = None
        try:
            self.key_thread_id = int(kernel32.GetCurrentThreadId())
            u.PeekMessageW(ctypes.byref(wintypes.MSG()), None, 0, 0, 0)
            def pressed(code, wparam, lparam):
                if code >= 0 and int(wparam) in (0x100, 0x104, 0x101, 0x105) and self.mode == 'control' and not self.control_stop.is_set():
                    self.control_stop.set()
                    self.online_stop.set()
                    self.post('status', '检测到键盘输入，已紧急停止鼠标控制')
                return u.CallNextHookEx(None, code, wparam, lparam)
            def scrolled(code, wparam, lparam):
                if code >= 0 and self.mode == 'control':
                    try:
                        event = ctypes.cast(lparam, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                        kind = int(wparam)
                        physical = not bool(event.flags & 0x01)
                        active = self.active_io
                        if physical and kind == 0x200 and active is not None:
                            now = time.monotonic()
                            recent = active.automatic_moves
                            while recent and now - recent[0][2] > max(.1, active.last_capture_ms / 1000. * 3.):
                                recent.popleft()
                            physical = not any(px == event.pt.x and py == event.pt.y for px, py, _ in recent)
                        if physical and self.mouse_monitor_armed.is_set() and kind in (0x200, 0x201, 0x202, 0x203, 0x204, 0x205, 0x206, 0x207, 0x208, 0x209, 0x20A, 0x20B, 0x20C, 0x20D, 0x20E):
                            self.control_stop.set()
                            self.mouse_monitor_armed.clear()
                            self.online_stop.set()
                            self.post('status', '检测到人工鼠标输入，已立即停止 AI 控制')
                        if kind == 0x20A and not physical:
                            delta = ctypes.c_short((event.mouseData >> 16) & 0xffff).value
                            with self.wheel_lock:
                                self.wheel_events.append(delta)
                    except Exception:
                        pass
                return u.CallNextHookEx(None, code, wparam, lparam)
            key_callback = KBDPROC(pressed)
            mouse_callback = MSPROC(scrolled)
            key_hook = u.SetWindowsHookExW(13, key_callback, None, 0)
            if not key_hook:
                self.post('status', '无法安装全局键盘安全钩子，鼠标控制已禁用')
                return
            mouse_hook = u.SetWindowsHookExW(14, mouse_callback, None, 0)
            if not mouse_hook:
                self.post('error', '鼠标安全钩子无法启动，已禁止自动控制')
                return
            self.wheel_hook_ready = True
            self.keyboard_ready.set()
            msg = wintypes.MSG()
            while not self.exit_stop.is_set():
                result = u.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if result <= 0:
                    break
        except Exception as ex:
            self.post('status', '键盘安全监控异常：' + str(ex)[:85])
        finally:
            self.keyboard_ready.clear()
            self.wheel_hook_ready = False
            self.mouse_monitor_armed.clear()
            if mouse_hook:
                u.UnhookWindowsHookEx(mouse_hook)
            if key_hook:
                u.UnhookWindowsHookEx(key_hook)
            self.key_thread_id = None
            if self.mode == 'control':
                self.emergency_stop('键盘安全监控已退出，鼠标控制立即停止')

    def create_meta(self, now, region, cursor, prior, held, scroll, dt, diff):
        x, y, w, h = region
        px, py = cursor
        vx = (px - prior[0]) / max(.001, dt)
        vy = (py - prior[1]) / max(.001, dt)
        scale = speed_reference(region, dt)
        speed = min(1., math.hypot(vx, vy) / scale)
        normalized_scroll = scroll / 120.
        history = list(self.control_history)
        total = len(history)
        if total:
            weights = [index + 1 for index in range(total)]
            denom = sum(weights)
            recent = [sum(row[column] * weight for row, weight in zip(history, weights)) / denom for column in range(4)]
        else:
            recent = [0.] * 4
        return [*recent,
                min(1., max(0., (px - x) / max(1, w))), min(1., max(0., (py - y) / max(1, h))),
                max(-1., min(1., vx / scale)), max(-1., min(1., vy / scale)), speed,
                float(held['l']), float(held['r']), float(held['m']),
                max(-1., min(1., normalized_scroll)), min(1., abs(normalized_scroll) / max(.001, dt)),
                dt / (1. + dt), w / max(1., w + h), math.sqrt(max(0., diff)),
                float(scroll != 0), *self.environment_code]

    def schedule_checkpoint(self):
        if self.brain is None or (self.saver is not None and self.saver.is_alive()):
            return
        brain = self.brain
        def persist():
            try:
                if isinstance(brain, RemoteBrain):
                    brain.checkpoint()
                else:
                    brain.save()
                self.last_checkpoint_step = self.iterations
            except Exception as ex:
                self.post('error', '定期保存失败：' + str(ex)[:110])
        self.saver = threading.Thread(target=persist, daemon=True)
        self.saver.start()

    def control_job(self, hwnd):
        io = None
        ticks = 0
        last_experience = None
        feedback = Feedback()
        infer_times = deque(maxlen=96)
        capture_times = deque(maxlen=96)
        frame_times = deque(maxlen=96)
        stop = AnyStop(self.control_stop, self.exit_stop)
        try:
            self.load(self.control_stop)
            if stop.is_set():
                return
            io = WindowsIO(hwnd)
            self.active_io = io
            io.activate()
            self.control_stop.wait(.2)
            if stop.is_set():
                return
            if not io.foreground():
                self.post('status', '目标窗口未获得前台焦点，已停止')
                return
            region = io.region()
            if region is None:
                self.post('status', '窗口无有效可交互区域，已停止')
                return
            io.prepare_cursor(region, stop)
            prev_frame = io.image(region)
            previous_epoch = io.capture_epoch
            invalid_frames = 0
            prev_pos = io.cursor()
            prev_dt = .075
            prev_change = 0.
            last_scroll = 0
            last_tick = time.monotonic()
            self.last_checkpoint_step = self.iterations
            self.control_history.clear()
            holdout_mode = False
            holdout_remaining = max(8, int(math.sqrt(REPLAY_LIMIT)))
            self.audit_sum = 0.
            self.audit_samples = 0
            self.start_online()
            if not self.keyboard_ready.is_set() or not self.wheel_hook_ready:
                raise RuntimeError('键盘或鼠标安全监控已退出，禁止自动控制')
            self.control_heartbeat = time.monotonic()
            self.mouse_monitor_armed.set()
            self.post('status', 'AI 正在选定窗口中探索并学习；任意键立即停止；学习反馈不是任务完成的保证')
            while not stop.is_set():
                if not self.keyboard_ready.is_set() or not self.wheel_hook_ready:
                    raise RuntimeError('输入安全监控已失效，停止自动控制')
                if self.online_error is not None:
                    issue = self.online_error
                    self.online_error = None
                    self.recover_learning_backend(issue)
                    if stop.is_set():
                        raise InterruptedError('后端恢复期间收到急停')
                    io.prepare_cursor(region, stop)
                    self.control_heartbeat = time.monotonic()
                    self.mouse_monitor_armed.set()
                    self.start_online()
                if io.keyboard_activity():
                    self.emergency_stop('检测到键盘输入，已紧急停止并释放鼠标')
                    raise InterruptedError('检测到键盘输入')
                start = time.monotonic()
                self.control_heartbeat = start
                tick_interval = max(.001, start - last_tick)
                dt = max(.015, min(.25, tick_interval))
                last_tick = start
                current_region = io.region()
                if current_region is None or not io.foreground():
                    raise RuntimeError('目标窗口已关闭、最小化或失去焦点，已停止控制')
                if current_region != region:
                    io.release()
                    region = current_region
                    io.prepare_cursor(region, stop)
                    prev_frame = io.image(region)
                    previous_epoch = io.capture_epoch
                    prev_pos = io.cursor()
                    prev_dt = .075
                    prev_change = 0.
                    self.post('status', '窗口区域已变化，正在按新位置和尺寸继续控制')
                io.safe(region, stop)
                frame = io.image(region)
                frame_stamp = io.last_capture_stamp
                frame_epoch = io.capture_epoch
                capture_ms = io.last_capture_ms
                if frame_epoch != previous_epoch:
                    prev_frame = frame
                    prev_change = 0.
                    previous_epoch = frame_epoch
                if not io.last_frame_valid:
                    invalid_frames += 1
                    if invalid_frames > max(12, int(math.sqrt(max(1, len(self.brain.memory))))):
                        raise RuntimeError('窗口持续无法采集一致的有效画面，已停止以避免误操作')
                    self.post('status', '捕获画面不完整或采集源切换中，暂不执行动作')
                    prev_frame = frame
                    prev_change = 0.
                    if stop.is_set():
                        break
                    self.control_stop.wait(min(.1, max(.015, capture_ms / 1000.)))
                    continue
                invalid_frames = 0
                mouse = io.cursor()
                held = io.keys()
                scroll = self.wheel_delta() if self.wheel_hook_ready else last_scroll
                meta = self.create_meta(start, region, mouse, prev_pos, held, scroll, prev_dt, prev_change)
                infer_start = time.monotonic()
                try:
                    action, ctrl = self.brain.choose(frame, meta, io.down)
                except Exception as ex:
                    self.recover_learning_backend(ex)
                    if stop.is_set():
                        raise InterruptedError('后端恢复期间收到急停')
                    io.prepare_cursor(region, stop)
                    self.control_heartbeat = time.monotonic()
                    self.mouse_monitor_armed.set()
                    action, ctrl = self.brain.choose(frame, meta, io.down)
                infer_ms = (time.monotonic() - infer_start) * 1000
                history = sorted(infer_times)
                usual = history[len(history) // 2] if history else 0.
                infer_times.append(infer_ms)
                self.watchdog_limit = max(3., (usual + capture_ms) * .012)
                self.control_heartbeat = time.monotonic()
                if stop.is_set():
                    raise InterruptedError('控制已停止')
                if infer_ms > max(750., usual * 5):
                    self.post('status', '模型推理延迟过高，已丢弃过期动作并重新采集窗口')
                    io.release()
                    prev_pos = mouse
                    prev_frame = frame
                    prev_dt = dt
                    prev_change = 0.
                    continue
                if ctrl is None:
                    ctrl = anchor_control(action)
                if action not in candidates(io.down):
                    raise RuntimeError('模型产生了不允许的动作')
                if len(ctrl) != CTRL_N or not all(math.isfinite(v) for v in ctrl):
                    raise RuntimeError('模型动作参数异常')
                io.safe(region, stop)
                duration = max(.015, min(.25, ctrl[7] * .25))
                execution_start = time.monotonic()
                outcome = io.act(normalize_control(ctrl), region, stop, duration)
                outcome['requested_action'] = action
                outcome['intended_ctrl'] = normalize_control(ctrl)
                if self.control_stop.wait(max(0., duration - (time.monotonic() - execution_start))) or stop.is_set():
                    break
                if io.region() != region:
                    updated = io.region()
                    if updated is None or not io.foreground():
                        raise RuntimeError('窗口区域已失效，停止控制')
                    io.release()
                    region = updated
                    io.prepare_cursor(region, stop)
                    prev_frame = io.image(region)
                    previous_epoch = io.capture_epoch
                    prev_pos = io.cursor()
                    prev_dt = .075
                    prev_change = 0.
                    continue
                io.safe(region, stop)
                capture_after = time.monotonic()
                nxt = io.fresh_image(region, capture_after, frame_epoch, stop)
                capture_times.append(capture_ms + io.last_capture_ms)
                if nxt is None or io.capture_epoch != frame_epoch or not io.last_frame_valid:
                    previous_epoch = io.capture_epoch
                    prev_frame = io.image(region)
                    prev_pos = io.cursor()
                    prev_dt = dt
                    prev_change = 0.
                    self.post('status', '动作后的新帧未到达或捕获源发生切换，已丢弃本次训练样本')
                    continue
                frame_times.append(tick_interval)
                new_mouse = io.cursor()
                reward, change, _ = feedback.assess(frame, nxt, prev_frame, outcome, new_mouse, region)
                self.audit_sum += reward
                self.audit_samples += 1
                actual_dt = max(.001, min(2., io.last_capture_stamp - frame_stamp))
                new_scroll = self.wheel_delta() if self.wheel_hook_ready else outcome['scroll']
                nmeta = self.create_meta(time.monotonic(), region, new_mouse, mouse, io.keys(), new_scroll, actual_dt, change)
                if holdout_remaining <= 0:
                    holdout_mode = not holdout_mode
                    block = max(8, int(math.sqrt(max(1, len(self.brain.memory)))))
                    holdout_remaining = block if holdout_mode else block * 3
                holdout_remaining -= 1
                try:
                    self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'], ctrl, outcome['action'], outcome['efficacy'], holdout_mode)
                except Exception as error:
                    self.recover_learning_backend(error)
                    if stop.is_set():
                        raise InterruptedError('后端恢复期间收到急停')
                    io.prepare_cursor(region, stop)
                    self.control_heartbeat = time.monotonic()
                    self.mouse_monitor_armed.set()
                    self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'], ctrl, outcome['action'], outcome['efficacy'], holdout_mode)
                self.control_history.append((outcome['ctrl'][0] * outcome['ctrl'][2], outcome['ctrl'][1] * outcome['ctrl'][2], outcome['ctrl'][6], reward))
                last_experience = ticks
                ticks += 1
                self.iterations += 1
                executed = outcome['ctrl']
                buttons = io.down.copy()
                wheel_speed = outcome['scroll'] / max(.001, actual_dt)
                self.post('control', f'方向 ({executed[0]:+.2f}, {executed[1]:+.2f}) · 速率 {outcome["moved"] / max(.001, duration):.0f}px/s · 左键 {"按下" if buttons["l"] else "释放"} · 右键 {"按下" if buttons["r"] else "释放"} · 滚轮键 {"按下" if buttons["m"] else "释放"} · 滚动速率 {wheel_speed:+.0f}/s · 滚动指令 {ctrl[6]:+.2f} · 决策 {action} / 实际 {outcome["action"]}')
                if ticks % 32 == 0:
                    def p95(samples):
                        ordered = sorted(samples)
                        return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * .95))] if ordered else 0.
                    fps = len(frame_times) / max(.001, sum(frame_times))
                    perf = self.brain.latest_perf if isinstance(self.brain, RemoteBrain) else {}
                    gpu_training = f' · 训练 {perf["training_samples_per_second"]:.1f}样本/s · 传输 {perf["transfer_ms"]:.1f}ms' if perf and self.brain.accelerated else ''
                    self.post('stats', f'经验 {len(self.brain.memory)} · 操作 {self.iterations} · 画面响应 {feedback.effects}/{feedback.total} · 可控进展 {feedback.progress_effects} · 可预测变化 {feedback.predictable_effects} · 无效 {feedback.blocks} · FPS {fps:.1f} · 推理P95 {p95(infer_times):.0f}ms · 采集P95 {p95(capture_times):.0f}ms' + gpu_training)
                with self.brain.save_lock:
                    saved_count = len(self.brain.memory)
                if self.iterations - self.last_checkpoint_step >= max(2, int(math.sqrt(max(1, saved_count)))):
                    self.schedule_checkpoint()
                prev_frame = frame
                prev_pos = mouse
                prev_change = change
                prev_dt = actual_dt
                last_scroll = outcome['scroll']
            if self.control_stop.is_set():
                self.post('status', '鼠标控制已停止；可再次开始或让 AI 睡眠学习')
        except InterruptedError:
            self.post('status', '紧急停止已执行')
        except RuntimeError as ex:
            self.post('status', str(ex)[:150])
        except Exception as ex:
            self.post('error', str(ex)[:170])
        finally:
            self.mouse_monitor_armed.clear()
            self.control_heartbeat = 0.
            self.online_stop.set()
            if io is not None:
                try:
                    io.halt()
                except Exception:
                    pass
                self.active_io = None
                self.post('control', '鼠标控制已停止 · 左/右/滚轮键已请求释放 · 滚动速率 0')
            if self.online_worker is not None and self.online_worker.is_alive():
                self.online_worker.join(timeout=5)
                if self.online_worker.is_alive():
                    self.post('error', '后台训练未及时结束，保存之前的经验')
            if io is not None:
                try:
                    io.close()
                except Exception as ex:
                    self.post('error', '鼠标释放失败：' + str(ex)[:115])
            if self.brain is not None:
                try:
                    if last_experience is not None and self.brain.memory:
                        if isinstance(self.brain, RemoteBrain):
                            self.brain.mark_last_done()
                        else:
                            with self.brain.save_lock:
                                last = self.brain.memory.pop()
                                self.brain.memory.append((*last[:6], True, *last[7:]))
                    if self.saver is not None and self.saver.is_alive():
                        self.saver.join()
                    self.brain.save()
                except Exception as ex:
                    self.post('error', '模型保存失败：' + str(ex)[:130])
            if self.audit_samples:
                try:
                    path = self.data_folder / 'performance.gz'
                    audit = read_json(path, {})
                    previous = audit.get('last') if isinstance(audit, dict) else None
                    previous_sleep = bool(audit.get('pending_sleep')) if isinstance(audit, dict) else False
                    quality = self.audit_sum / self.audit_samples
                    current_metrics = {'frames': self.audit_samples, 'mean': quality, 'timestamp': time.time(), 'efficacy': feedback.efficacy_total / max(1, feedback.total), 'progress_rate': feedback.progress_effects / max(1, feedback.total), 'repetition_rate': feedback.repeats / max(1, feedback.total), 'blocked_rate': feedback.blocks / max(1, feedback.total)}
                    comparison = ''
                    if previous_sleep and isinstance(previous, dict) and previous.get('frames', 0) > 0:
                        keys = [('mean', '平均反馈'), ('efficacy', '动作执行率'), ('progress_rate', '可控进展率'), ('repetition_rate', '重复率'), ('blocked_rate', '受阻率')]
                        differences = [f'{label} {previous[key]:+.3f}→{current_metrics[key]:+.3f}' for key, label in keys if key in previous]
                        comparison = '；睡眠前后同环境 ' + '、'.join(differences) + '（均非任务成功率）'
                    self.data_folder.mkdir(parents=True, exist_ok=True)
                    save_json(path, {'last': current_metrics, 'pending_sleep': False})
                    if comparison:
                        self.post('status', '控制已结束' + comparison)
                except (OSError, ValueError, TypeError) as ex:
                    self.post('error', '表现记录未保存：' + str(ex)[:110])
            self.post('done', 'control')

    def sleep(self):
        if self.mode == 'sleep':
            self.status.set('AI 正在睡眠训练中')
            return
        if self.mode == 'closed':
            return
        previous = self.worker if self.worker is not None and self.worker.is_alive() else None
        self.emergency_stop(None)
        self.sleep_stop.clear()
        self.mode = 'sleep'
        self.worker = threading.Thread(target=self.sleep_job, args=(previous,), daemon=True)
        self.worker.start()

    def sleep_job(self, previous):
        try:
            if previous is not None and previous is not threading.current_thread():
                previous.join(timeout=12)
                if previous.is_alive():
                    raise RuntimeError('前一个控制任务未及时结束，已取消睡眠训练')
            if self.online_worker is not None and self.online_worker.is_alive():
                self.online_worker.join(timeout=5)
                if self.online_worker.is_alive():
                    raise RuntimeError('在线训练尚未结束，本次睡眠训练已取消')
            if self.saver is not None and self.saver.is_alive():
                self.saver.join(timeout=8)
                if self.saver.is_alive():
                    raise RuntimeError('模型正在保存，已取消本次睡眠训练')
            if self.exit_stop.is_set():
                return
            if self.brain is not None and self.brain_folder == self.data_folder:
                has_experience = bool(self.brain.memory)
            else:
                has_experience = any(bool(records) for _, _, records in replay_sources(self.data_folder))
            if not has_experience:
                self.post('status', '尚无交互经验；先点击绿色按钮让 AI 感知并探索窗口')
                return
            self.load(self.sleep_stop)
            if self.sleep_stop.is_set() or self.exit_stop.is_set():
                return
            mem = len(self.brain.memory)
            if not mem:
                self.post('status', '没有可训练的交互经验，本次不启动睡眠训练')
                return
            self.post('status', f'AI 睡眠中：正在巩固 {mem} 条交互经验…')
            if hasattr(self.brain, 'begin_sleep'):
                self.brain.begin_sleep()
            start = time.monotonic()
            steps = 0
            validation = sleep_split(list(self.brain.memory))
            if validation is None:
                if hasattr(self.brain, 'end_sleep'):
                    self.brain.end_sleep()
                self.post('status', '尚未收集足够的预留验证经验，本次不训练，避免用在线学习过的数据误判提升')
                return
            ceiling = mem * max(2, int(math.log2(1. + mem)))
            training_latency = getattr(self.brain, 'training_latency', {}).get(True, 0.) if hasattr(self.brain, 'training_latency') else 0.
            max_duration = max(15., min(180., math.sqrt(mem) * max(1., training_latency * math.sqrt(mem))))
            check_span = max(8, int(math.sqrt(mem)))
            best_loss = None
            changes = deque(maxlen=max(3, int(math.log2(1. + mem))))
            next_check = check_span
            while steps < ceiling and time.monotonic() - start < max_duration and not self.sleep_stop.is_set() and not self.exit_stop.is_set():
                chunk = min(check_span, ceiling - steps)
                try:
                    n = self.brain.train(chunk, self.sleep_stop)
                except Exception as ex:
                    self.recover_learning_backend(ex)
                    self.post('status', '训练后端发生变化，已取消本轮睡眠以避免未经验证的模型更新')
                    return
                steps += n
                if n == 0:
                    break
                if steps >= next_check and hasattr(self.brain, 'sleep_progress'):
                    self.post('stats', f'经历 {mem} 帧 · 睡眠巩固 {steps}/{ceiling} 步')
                    next_check = steps + check_span
                    loss = self.brain.sleep_progress()
                    if loss is not None:
                        improvement = 0. if best_loss is None else max(0., best_loss - loss)
                        changes.append(improvement)
                        if best_loss is None or loss < best_loss:
                            best_loss = loss
                        if len(changes) == changes.maxlen and sum(changes) <= (abs(best_loss) + 1e-8) / math.sqrt(mem):
                            break
            result = self.brain.end_sleep() if hasattr(self.brain, 'end_sleep') else None
            self.brain.save()
            if result is not None and result[0] is True:
                path = self.data_folder / 'performance.gz'
                audit = read_json(path, {})
                if isinstance(audit, dict) and isinstance(audit.get('last'), dict):
                    audit['pending_sleep'] = True
                    save_json(path, audit)
            interrupted = self.sleep_stop.is_set() or self.exit_stop.is_set()
            prefix = '提前唤醒' if interrupted else '自然唤醒'
            positive = sum(row[5] > 0. for row in self.brain.memory)
            rate = 100 * positive / max(1, len(self.brain.memory))
            behavior = ''
            if result is not None and len(result) >= 5 and result[3] is not None and result[4] is not None:
                behavior = f'，留出经验的反馈偏好 {100 * result[3]:.0f}% → {100 * result[4]:.0f}%'
            if result is not None and result[0] is False:
                self.post('status', f'AI {prefix}；离线验证退化，已回滚训练（{steps} 步）{behavior}；历史正反馈 {rate:.1f}%')
            elif result is not None and result[0] is None:
                self.post('status', f'AI {prefix}；没有验证到可靠提升，已保留原模型（{steps} 步）{behavior}；实际能力待验证')
            elif result is not None:
                self.post('status', f'AI {prefix}；预留经验验证通过（{steps} 步），离线误差 {result[1]:.4f} → {result[2]:.4f}{behavior}；真实任务能力仍需验证')
            else:
                self.post('status', f'AI {prefix}；未进行未经验证的模型更新；历史正反馈 {rate:.1f}%')
        except Exception as ex:
            self.post('error', '睡眠学习失败：' + str(ex)[:150])
        finally:
            self.post('done', 'sleep')

    def wake(self):
        if self.mode == 'sleep':
            self.sleep_stop.set()
            if isinstance(self.brain, RemoteBrain):
                self.brain.cancel_train()
            self.status.set('正在取消后续训练批次并保存经验…')
        else:
            self.status.set('AI 当前没有睡觉')

    def close(self):
        if self.mode == 'closed':
            return
        self.mode = 'closed'
        if self.refresh_after is not None:
            try:
                self.root.after_cancel(self.refresh_after)
            except tk.TclError:
                pass
            self.refresh_after = None
        self.close_started = time.monotonic()
        self.backend_recovering.clear()
        self.emergency_stop(None)
        self.sleep_stop.set()
        self.exit_stop.set()
        self.status.set('正在释放鼠标并保存学习数据…')
        if os.name == 'nt' and self.key_thread_id is not None:
            try:
                u.PostThreadMessageW(self.key_thread_id, 0x12, 0, 0)
            except Exception:
                pass
        self.root.after(40, self.finish_close)

    def emergency_snapshot(self):
        brain = self.brain
        if brain is None:
            return
        try:
            with brain.save_lock:
                records = list(brain.memory)
                generation = max(brain.generation, getattr(brain, 'latest_replay_generation', 0), getattr(brain, 'model_generation', 0)) + 2
            if records:
                brain.folder.mkdir(parents=True, exist_ok=True)
                save_replay(brain.folder, records, 'recovery', generation)
        except Exception as error:
            self.exit_backup_error = str(error)[:150]

    def finish_close(self):
        elapsed = time.monotonic() - self.close_started
        active = self.active_io
        if active is not None:
            try:
                active.halt()
            except Exception:
                pass
        busy = any(thread is not None and thread.is_alive() for thread in (self.worker, self.saver, self.online_worker))
        if busy and elapsed < max(8., self.watchdog_limit * 3.):
            self.root.after(100, self.finish_close)
            return
        if busy and self.exit_backup is None:
            self.status.set('后台任务停止较慢，正在单独保存可恢复的交互经验…')
            self.exit_backup = threading.Thread(target=self.emergency_snapshot, daemon=False)
            self.exit_backup.start()
        if self.exit_backup is not None and self.exit_backup.is_alive():
            self.root.after(100, self.finish_close)
            return
        if self.exit_backup_error is not None:
            self.status.set('紧急备份失败：' + self.exit_backup_error)
        if isinstance(self.brain, RemoteBrain):
            try:
                self.brain.close()
            except Exception:
                pass
        if busy:
            self.status.set('后台任务未在安全时限内结束，已请求释放输入并终止独立计算进程')
        self.root.destroy()

    def run(self):
        self.root.mainloop()


if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == '--mouseai-hardware-probe':
        if hardware_probe(sys.argv[2], sys.argv[3]):
            print('READY')
        else:
            sys.exit(1)
    else:
        MouseAIApp().run()
