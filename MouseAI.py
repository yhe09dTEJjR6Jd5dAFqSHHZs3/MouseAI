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
META_N = 18
MAX_REPLAY_RECORDS = 4500
REPLAY_MAGIC = b'MOUSEAI6'
REPLAY_PACK = struct.Struct('<Bf?f' + 'f' * (META_N * 2 + CTRL_N))

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
    return max(384, min(MAX_REPLAY_RECORDS, int(available * .035 / (VIS_N * 2 + REPLAY_PACK.size)) if available else MAX_REPLAY_RECORDS))

REPLAY_LIMIT = replay_capacity()
MAX_SPEED = 820.
ACT = [(0, 0, 0, '', 0)]
for magnitude in (280, 620):
    for angle in range(8):
        a = angle * math.pi / 4
        ACT.append((math.cos(a), math.sin(a), magnitude, '', 0))
ACT += [(0, 0, 0, 'l+', 0), (0, 0, 0, 'l-', 0), (0, 0, 0, 'r+', 0), (0, 0, 0, 'r-', 0), (0, 0, 0, 'm+', 0), (0, 0, 0, 'm-', 0), (0, 0, 0, '', 120), (0, 0, 0, '', -120), (0, 0, 0, '', 240), (0, 0, 0, '', -240)]
ACT_N = len(ACT)

class AnyStop:
    def __init__(self, *events):
        self.events = events

    def is_set(self):
        return any(event.is_set() for event in self.events)


def candidates(held):
    allowed = list(range(17))
    for i, (b, press) in enumerate((('l', True), ('l', False), ('r', True), ('r', False), ('m', True), ('m', False)), 17):
        if bool(held.get(b, False)) != press:
            allowed.append(i)
    allowed.extend(range(23, ACT_N))
    return allowed


def operational_candidates(held, steps):
    allowed = candidates(held)
    if steps < ACT_N:
        return [i for i in allowed if i < 17]
    if steps < ACT_N * len(('l', 'r', 'm')):
        return [i for i in allowed if i < 17 or i >= 23 or i in (17, 18)]
    return allowed


def explore_action(allowed, meta=None, steps=0):
    move = [i for i in allowed if i < 17]
    scroll = [i for i in allowed if i >= 23]
    buttons = [i for i in allowed if 17 <= i < 23]
    change = float(meta[16]) if meta is not None else 0.
    stagnation = max(0., 1. - min(1., change * 90))
    move_weight = .9 - .12 * stagnation
    scroll_weight = .08 + .07 * stagnation
    button_weight = .02 + .05 * stagnation
    if meta is not None and any(float(meta[i]) > .5 for i in (9, 10, 11)):
        button_weight += .13
    if meta is not None and min(float(meta[4]), float(meta[5]), 1. - float(meta[4]), 1. - float(meta[5])) < .07:
        button_weight *= .1
        scroll_weight *= .5
    groups = [(move, move_weight), (scroll, scroll_weight), (buttons, button_weight)]
    available = [(group, weight) for group, weight in groups if group]
    pick = random.random() * sum(weight for group, weight in available)
    for group, weight in available:
        pick -= weight
        if pick <= 0:
            return random.choice(group)
    return random.choice(available[-1][0])



def anchor_control(action, prediction=None, trust=.45):
    ax, ay, speed, button, wheel = ACT[action]
    ctrl = [float(ax), float(ay), float(speed / MAX_SPEED), 0., 0., 0., float(wheel / 240), .45]
    if button:
        ctrl[{'l': 3, 'r': 4, 'm': 5}[button[0]]] = 1. if button[1] == '+' else -1.
    if prediction is not None:
        trust = max(0., min(.98, float(trust)))
        if 1 <= action <= 16:
            dx = (1 - trust) * ax + trust * max(-1., min(1., float(prediction[0])))
            dy = (1 - trust) * ay + trust * max(-1., min(1., float(prediction[1])))
            norm = math.hypot(dx, dy)
            if norm > 1e-6:
                ctrl[0], ctrl[1] = dx / norm, dy / norm
            ctrl[2] = max(.02, min(1., (1 - trust) * ctrl[2] + trust * max(0., min(1., float(prediction[2])))))
        elif action >= 23:
            predicted_wheel = max(-1., min(1., float(prediction[6])))
            ctrl[6] = math.copysign(max(.08, (1 - trust) * abs(ctrl[6]) + trust * abs(predicted_wheel)), wheel)
        ctrl[7] = max(.05, min(1., (1 - trust) * ctrl[7] + trust * max(0., min(1., float(prediction[7])))))
    return tuple(ctrl)


def exploratory_control(action):
    ctrl = list(anchor_control(action))
    if 1 <= action <= 16:
        angle = math.atan2(ctrl[1], ctrl[0]) + random.uniform(-math.pi / len(ACT[:17]), math.pi / len(ACT[:17]))
        ctrl[0], ctrl[1] = math.cos(angle), math.sin(angle)
        ctrl[2] = max(.02, min(1., ctrl[2] * math.exp(random.gauss(0., .35))))
    elif action >= 23:
        ctrl[6] *= random.uniform(.5, 1.)
    ctrl[7] = random.uniform(.15, .9)
    return tuple(ctrl)


def sleep_split(records):
    count = len(records)
    if count < 60:
        return None
    border = min(count - 8, max(40, int(count * .85)))
    return records[:max(32, border - 5)], records[border:]


def quarantine(path):
    if path.exists():
        try:
            os.replace(path, path.with_name(path.name + '.damaged'))
        except OSError:
            pass

def session_signature(image):
    chunks = bytearray()
    for y in range(0, VIS_H, 9):
        for x in range(0, VIS_W, 16):
            colors = []
            for channel in range(CHANNELS):
                base = channel * PIXELS
                colors.append(sum(sum(image[base + (y + j) * VIS_W + x:base + (y + j) * VIS_W + x + 16]) for j in range(9)) // 144)
            chunks.extend(colors)
    return hashlib.blake2s(chunks, digest_size=8).digest()


class Feedback:
    def __init__(self):
        self.frequency = {}
        self.sequence = deque(maxlen=12)
        self.background = .005
        self.visited = {}
        self.total = 0
        self.effects = 0
        self.blocks = 0
        self.repeats = 0

    def assess(self, old, new, previous, outcome, pointer, region):
        visible = PIXELS * CHANNELS
        dist = sum(abs(a - b) for a, b in zip(old[:visible], new[:visible])) / (visible * 255)
        bg = sum(abs(a - b) for a, b in zip(previous[:visible], old[:visible])) / (visible * 255)
        self.background = .96 * self.background + .04 * bg
        attributable = max(0., dist - max(self.background * 1.2, bg * .8))
        signature = session_signature(new)
        sightings = self.frequency.get(signature, 0)
        novel = sightings == 0
        self.frequency[signature] = sightings + 1
        if len(self.frequency) > 4096:
            for key in list(self.frequency)[:1024]:
                self.frequency.pop(key, None)
        action = outcome['action']
        self.sequence.append(action)
        repetitive = len(self.sequence) >= 7 and len(set(list(self.sequence)[-7:])) == 1
        x, y, w, h = region
        cx = (pointer[0] - x) / max(1, w)
        cy = (pointer[1] - y) / max(1, h)
        at_edge = min(cx, cy, 1 - cx, 1 - cy) < .015
        visual_effect = attributable > max(.0025, self.background * .45) and sightings < 3 and outcome['changed']
        progress = min(.021, attributable * 1.25) / (1 + sightings) if visual_effect else 0.
        moved = outcome.get('moved', 0.)
        cell = (min(11, max(0, int(cx * 12))), min(7, max(0, int(cy * 8))))
        visits = self.visited.get(cell, 0)
        self.visited[cell] = visits + 1
        motion = min(.004, moved / max(w, h) * .07) / math.sqrt(1 + visits) if moved > 1 and not at_edge else 0.
        reward = -.002 + progress + motion
        if outcome['blocked']:
            reward -= .03
        if outcome['switches'] and attributable < .006:
            reward -= .008
        if outcome['scroll'] and attributable < .006:
            reward -= .008
        if repetitive:
            reward -= .016
        if outcome['changed'] and not visual_effect and not outcome.get('moved', 0.):
            reward -= .004
        if at_edge:
            reward -= .012
        if any(name[0] in ('r', 'm') and name.endswith('+') for name in outcome['switches']):
            reward -= .008
        self.total += 1
        self.effects += int(visual_effect)
        self.blocks += int(bool(outcome['blocked']))
        self.repeats += int(repetitive)
        return max(-.15, min(.08, reward)), dist, visual_effect


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
            if count > MAX_REPLAY_RECORDS or generation < 1:
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
                action, reward, done, dt = values[:4]
                numeric = values[4:]
                if action >= ACT_N or not math.isfinite(reward) or not .001 <= dt <= 2. or not all(math.isfinite(v) for v in numeric):
                    raise ValueError('经验数值无效')
                meta = tuple(numeric[:META_N])
                nmeta = tuple(numeric[META_N:META_N * 2])
                ctrl = tuple(numeric[META_N * 2:])
                records.append((ob, meta, action, nxt, nmeta, float(reward), bool(done), float(dt), ctrl))
            if f.read(32) != digest.digest() or f.read(1):
                raise ValueError('经验校验失败')
        return records, generation
    except (OSError, EOFError, ValueError, struct.error, MemoryError):
        return None


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
                for ob, meta, action, nxt, nmeta, reward, done, dt, ctrl in entries:
                    record = REPLAY_PACK.pack(action, reward, done, dt, *meta, *nmeta, *ctrl)
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
        for slot in (0, 1):
            pair = read_replay(folder, slot)
            if pair is None or pair[1] <= self.generation:
                continue
            data = read_json(folder / f'learning.{slot}.lite.gz', {})
            if not isinstance(data, dict) or data.get('version') != 6 or data.get('generation') != pair[1]:
                continue
            table = {}
            data_table = data.get('table')
            for key, value in (data_table.items() if isinstance(data_table, dict) else []):
                try:
                    keybytes = bytes.fromhex(key)
                    if len(keybytes) in (69, 14, 13) and len(value) == ACT_N and all(math.isfinite(float(v)) for v in value):
                        table[keybytes] = [float(v) for v in value]
                except (TypeError, ValueError, OverflowError):
                    continue
            self.table = table
            try:
                steps = max(0, int(data.get('steps', 0)))
            except (TypeError, ValueError, OverflowError):
                continue
            self.steps = steps
            self.memory, self.generation, self.slot = pair[0], pair[1], slot
        recovered = [(pair[1], slot, pair[0]) for slot in (0, 1) if (pair := read_replay(folder, slot)) is not None]
        if recovered:
            generation, slot, records = max(recovered, key=lambda entry: entry[0])
            self.latest_replay_generation = generation
            if generation > self.generation:
                self.memory = records
                self.steps = max(self.steps, len(records))
                if self.slot < 0:
                    self.slot = slot
        if self.memory and not self.table:
            self.rebuild_from_memory()

    def rebuild_from_memory(self):
        with self.save_lock:
            self.table.clear()
            for row in self.memory:
                self.update(row)

    def restore_experience(self, records, steps):
        with self.save_lock:
            self.memory = deque(records, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.rebuild_from_memory()

    def key(self, ob, meta):
        out = []
        for r in range(0, VIS_H, 9):
            for c in range(0, VIS_W, 16):
                sums = [0, 0, 0]
                for channel in range(CHANNELS):
                    for y in range(r, r + 9):
                        start = channel * PIXELS + y * VIS_W + c
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
        groups = ((0, 1, 2, 3), (4, 5, 6, 7, 8), (9, 10, 11, 12, 13, 17), (14, 15, 16))
        for index, group in enumerate(groups):
            data = bytes([index]) + bytes(quantized[i] for i in group)
            tiles.append(b'T' + bytes([index]) + hashlib.blake2s(data + visual[index * 12:index * 12 + 12], digest_size=12).digest())
            tiles.append(b'U' + bytes([index]) + quantized[group[0]:group[0] + 1] + hashlib.blake2s(data, digest_size=10).digest())
        return tiles

    def values(self, ob, meta):
        values = [self.table[key] for key in self.keys(ob, meta) if key in self.table]
        if not values:
            return None
        return [sum(part[action] for part in values) / len(values) for action in range(ACT_N)]

    def choose(self, ob, meta, held):
        opts = operational_candidates(held, self.steps)
        with self.save_lock:
            value = self.values(ob, meta)
            epsilon = max(.1, .48 / (1 + self.steps / 2400))
            exploring = value is None or random.random() < epsilon
            if exploring:
                choice = explore_action(opts, meta, self.steps)
            else:
                choice = max(opts, key=lambda i: value[i] + random.uniform(-.012, .012) - (.04 if i >= 17 else 0))
        return choice, exploratory_control(choice) if exploring else anchor_control(choice)

    def update(self, row):
        ob, meta, action, nxt, nmeta, reward, done, dt = row[:8]
        before = self.values(ob, meta)
        after = self.values(nxt, nmeta)
        held = {'l': nmeta[9] > .5, 'r': nmeta[10] > .5, 'm': nmeta[11] > .5}
        future = max(after[i] for i in candidates(held)) if after else 0.
        target = reward + (0 if done else (.975 ** (dt / .075)) * future)
        baseline = before[action] if before is not None else 0.
        correction = .12 * (target - baseline)
        for key in self.keys(ob, meta):
            value = self.table.setdefault(key, [0.] * ACT_N)
            value[action] += correction
        if len(self.table) > 14000:
            for k in list(self.table)[:1800]:
                self.table.pop(k, None)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl):
        row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl))
        with self.save_lock:
            self.memory.append(row)
            self.update(row)
            self.steps += 1

    def train(self, count, stop):
        source = self.train_memory if self.train_memory is not None else self.memory
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
        useful = [row for row in records if row[2] != 0 and (row[5] > .004 or row[5] < -.012)]
        if len(useful) < 8:
            return None
        good = 0
        for row in useful:
            q = self.values(row[0], row[1]) or [0.] * ACT_N
            held = {'l': row[1][9] > .5, 'r': row[1][10] > .5, 'm': row[1][11] > .5}
            best = max(candidates(held), key=lambda a: q[a])
            good += (best == row[2]) if row[5] > .004 else (best != row[2])
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
            if len(self.memory) < 60:
                return
            records = list(self.memory)
            self.train_memory, validation = sleep_split(records)
            labels = self.validation_targets(validation)
            before = self.evaluate(validation, labels)
            quality = self.policy_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.table))

    def sleep_progress(self):
        with self.save_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality, snapshot = self.sleep_evaluation
            after = self.evaluate(records, labels)
            current = self.policy_metric(records)
            tolerance = max(1e-6, abs(before) * .002)
            if math.isfinite(after) and after + tolerance < before and (quality is None or current is None or current + .015 >= quality):
                if self.sleep_best is None or after + tolerance < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.table))
            return after

    def end_sleep(self):
        with self.save_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            after = self.sleep_progress()
            records, labels, before, quality, snapshot = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            current = self.policy_metric(records)
            if best is not None:
                self.table = best[2]
                return True, before, best[0], quality, best[1]
            self.table = snapshot
            degraded = not math.isfinite(after) or after > before + max(.0005, abs(before) * .08) or (quality is not None and current is not None and current + .015 < quality)
            return (False if degraded else None), before, after, quality, current

    def save(self):
        self.folder.mkdir(parents=True, exist_ok=True)
        with self.checkpoint_lock:
            with self.save_lock:
                memory = list(self.memory)
                generation = max(self.generation, self.latest_replay_generation) + 1
                slot = (self.slot + 1) % 2
                data = {'version': 6, 'generation': generation, 'steps': self.steps, 'table': {k.hex(): v[:] for k, v in self.table.items()}}
            save_replay(self.folder, memory, slot, generation)
            save_json(self.folder / f'learning.{slot}.lite.gz', data)
            with self.save_lock:
                self.generation, self.latest_replay_generation, self.slot = generation, generation, slot

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
        nn = torch.nn

        class Net(nn.Module):
            def __init__(self):
                super().__init__()
                self.vision = nn.Sequential(nn.Conv2d(CHANNELS * 2, 16, 5, stride=2, padding=2), nn.ReLU(), nn.Conv2d(16, 32, 3, stride=2, padding=1), nn.ReLU(), nn.Conv2d(32, 48, 3, stride=2, padding=1), nn.ReLU(), nn.AdaptiveAvgPool2d((4, 6)), nn.Flatten(), nn.Linear(48 * 4 * 6, 160), nn.ReLU())
                self.policy = nn.Sequential(nn.Linear(160 + META_N, 192), nn.GELU(), nn.Linear(192, ACT_N))
                self.control = nn.Sequential(nn.Linear(160 + META_N, 128), nn.GELU(), nn.Linear(128, ACT_N * CTRL_N), nn.Tanh())
                self.effect = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 160), nn.GELU(), nn.Linear(160, 1))

            def forward(self, frames, meta):
                embedding = torch.cat((self.vision(frames), meta), dim=1)
                raw = self.control(embedding).reshape(-1, ACT_N, CTRL_N)
                outputs = torch.cat((raw[..., :2], (raw[..., 2:3] + 1.) * .5, raw[..., 3:7], (raw[..., 7:8] + 1.) * .5), dim=-1)
                return self.policy(embedding), outputs, embedding

            def effect_value(self, embedding, controls):
                return self.effect(torch.cat((embedding, controls), dim=-1)).squeeze(-1)

        if getattr(device, 'type', None) == 'cuda':
            torch.backends.cudnn.benchmark = True
        self.q = Net().to(device)
        self.target = copy.deepcopy(self.q).to(device)
        self.target.eval()
        self.optq = torch.optim.AdamW(self.q.parameters(), lr=.00028, weight_decay=.0001)
        self.batch_sizes = {False: 16, True: 48}
        self.steps = 0
        self.grads = 0
        self.train_memory = None
        self.sleep_evaluation = None
        self.sleep_best = None
        pairs = []
        for slot in (0, 1):
            pair = read_replay(folder, slot)
            if pair is not None:
                pairs.append((pair[1], slot, pair[0]))
        for generation, slot, memory in sorted(pairs, reverse=True):
            path = folder / f'model.{slot}.pt'
            if not path.exists():
                continue
            try:
                state = torch.load(path, map_location='cpu', weights_only=True)
                if state.get('version') != 8 or state.get('generation') != generation:
                    continue
                self.q.load_state_dict(state['q'], strict=True)
                self.target.load_state_dict(state['target'], strict=True)
                self.optq.load_state_dict(state['opt'])
                for group in self.optq.state.values():
                    for key, value in group.items():
                        if torch.is_tensor(value):
                            group[key] = value.to(device)
                self.steps = max(0, int(state.get('steps', 0)))
                self.grads = max(0, int(state.get('grads', 0)))
                self.memory, self.generation, self.slot = memory, generation, slot
                break
            except Exception:
                continue
        if self.generation == 0:
            recovered = [(pair[1], slot, pair[0]) for slot in (0, 1) if (pair := read_replay(folder, slot)) is not None]
            if recovered:
                self.generation, self.slot, self.memory = max(recovered, key=lambda entry: entry[0])
                self.steps = max(self.steps, len(self.memory))
                if len(self.memory) >= 32:
                    self.train(min(32, max(1, int(math.sqrt(len(self.memory))))), AnyStop())
        self.q.eval()

    def images(self, observations):
        if any(len(im) != VIS_N for im in observations):
            raise ValueError('采集画面维度不匹配')
        raw = bytearray().join(observations)
        return self.t.frombuffer(raw, dtype=self.t.uint8).reshape(len(observations), CHANNELS * 2, VIS_H, VIS_W).to(device=self.d, dtype=self.t.float32).div_(255)

    def choose(self, ob, meta, held):
        allowed = operational_candidates(held, self.steps)
        epsilon = max(.09, .45 / (1 + self.steps / 2500))
        if random.random() < epsilon:
            action = explore_action(allowed, meta, self.steps)
            return action, exploratory_control(action)
        with self.model_lock:
            self.q.eval()
            with self.t.no_grad():
                q, output, embedding = self.q(self.images([ob]), self.t.tensor([meta], dtype=self.t.float32, device=self.d))
                values = q[0].detach().cpu().tolist()
        action = max(allowed, key=lambda i: values[i] + random.uniform(-.01, .01) - (.04 if i >= 17 else 0))
        control = output[0, action].detach().cpu().tolist()
        confidence = self.grads / (self.grads + max(1, math.sqrt(self.steps)))
        trust = min(.98, confidence * self.steps / (self.steps + 24))
        return action, anchor_control(action, control, trust)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl):
        with self.save_lock:
            self.memory.append((ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl)))
            self.steps += 1

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.train_memory if self.train_memory is not None else self.memory)
        if len(source) < 32:
            return 0
        with self.model_lock:
            self.q.train()
            try:
                return self._train_locked(count, stop, source)
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
            qvalues, predicted_all, embedding = self.q(state, meta)
            values = qvalues.gather(1, acts.unsqueeze(1)).squeeze(1)
            predicted = predicted_all.gather(1, acts[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
            effectiveness = self.q.effect_value(embedding, ctrl)
            with t.no_grad():
                online, _, _ = self.q(future, nmeta)
                mask = t.zeros_like(online, dtype=t.bool)
                for index, column in ((17, 9), (19, 10), (21, 11)):
                    down = nmeta[:, column] > .5
                    mask[:, index] = down
                    mask[:, index + 1] = ~down
                online = online.masked_fill(mask, -1e8)
                best = online.argmax(dim=1, keepdim=True)
                next_q, next_controls, next_features = self.target(future, nmeta)
                after = next_q.gather(1, best).squeeze(1)
                next_ctrl = next_controls.gather(1, best.unsqueeze(-1).expand(-1, 1, CTRL_N)).squeeze(1)
                next_effect = self.target.effect_value(next_features, next_ctrl)
                discount = (.975 ** (dt / .075)) * (1 - done)
                targets = rew + discount * after
                effect_targets = rew + discount * next_effect
            temporal = t.nn.functional.smooth_l1_loss(values, targets)
            effect_loss = t.nn.functional.smooth_l1_loss(effectiveness, effect_targets)
            advantage = (rew - effectiveness.detach()).clamp(-.1, .1)
            good = t.nn.functional.softplus(advantage * 24) / 24
            auxiliary = ((predicted - ctrl).square().mean(dim=1) * good).mean()
            for param in self.q.effect.parameters():
                param.requires_grad_(False)
            actor_gain = self.q.effect_value(embedding, predicted).mean()
            for param in self.q.effect.parameters():
                param.requires_grad_(True)
            loss = temporal + .4 * effect_loss + .04 * auxiliary - .02 * actor_gain
            if not bool(t.isfinite(loss).item()):
                raise ValueError('模型训练数值异常')
            self.optq.zero_grad(set_to_none=True)
            loss.backward()
            t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.0)
            self.optq.step()
            self.grads += 1
            if self.grads % 8 == 0:
                with t.no_grad():
                    for target_param, param in zip(self.target.parameters(), self.q.parameters()):
                        target_param.lerp_(param, .04)
            elapsed = max(.001, time.monotonic() - started)
            if getattr(self.d, 'type', None) == 'cuda':
                if self.grads % 8 == 1:
                    self.batch_started = started
                if self.grads % 8 == 0:
                    t.cuda.synchronize(self.d)
                    elapsed = max(.001, (time.monotonic() - self.batch_started) / 8)
                else:
                    elapsed = None
            if elapsed is not None:
                budget = .07 if not sleeping else .2
                ratio = max(.7, min(1.45, math.sqrt(budget / elapsed)))
                self.batch_sizes[sleeping] = max(8, min(192, int(self.batch_sizes[sleeping] * ratio + .5)))
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
                qvalue = self.q(frames, meta)[0].gather(1, actions.unsqueeze(1)).squeeze(1)
                target = t.tensor(labels[start:start + len(segment)], dtype=t.float32, device=self.d)
                total += float(t.nn.functional.smooth_l1_loss(qvalue, target, reduction='sum').cpu())
        return total / max(1, len(entries))

    def policy_metric(self, records):
        examples = [r for r in records if r[2] != 0 and (r[5] > .004 or r[5] < -.012)]
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
                    total += (chosen == row[2]) if row[5] > .004 else (chosen != row[2])
        return total / len(examples)

    def begin_sleep(self):
        with self.save_lock:
            records = list(self.memory)
        with self.model_lock:
            self.train_memory = None
            self.sleep_evaluation = None
            self.sleep_best = None
            if len(records) < 60:
                return
            self.train_memory, validation = sleep_split(records)
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
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads)

    def sleep_progress(self):
        with self.model_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality = self.sleep_evaluation[:4]
            after = self.evaluate(records, labels)
            current = self.policy_metric(records)
            tolerance = max(1e-6, abs(before) * .002)
            if math.isfinite(after) and after + tolerance < before and (quality is None or current is None or current + .025 >= quality):
                if self.sleep_best is None or after + tolerance < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads)
            return after

    def end_sleep(self):
        with self.model_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            after = self.sleep_progress()
            records, labels, before, quality, old_q, old_target, old_opt, old_grads = self.sleep_evaluation
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
                    generation = max(self.generation, checkpoint_generation or 0) + 1
                    slot = (checkpoint_slot + 1) % 2 if checkpoint_slot is not None else (self.slot + 1) % 2
                    steps = self.steps
                    snapshot = {'version': 8, 'generation': generation, 'q': cpu_copy(self.q.state_dict()), 'target': cpu_copy(self.target.state_dict()), 'opt': cpu_copy(self.optq.state_dict()), 'steps': steps, 'grads': self.grads}
            path = self.folder / f'model.{slot}.pt'
            tmp = self.folder / f'model.{slot}.pt.tmp'
            try:
                with open(tmp, 'wb') as raw:
                    self.t.save(snapshot, raw)
                    raw.flush()
                    os.fsync(raw.fileno())
                save_replay(self.folder, memory, slot, generation)
                os.replace(tmp, path)
                with self.save_lock:
                    self.generation, self.slot = generation, slot
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
        with torch.no_grad():
            online = model(frames, meta)[0]
            masked = torch.ones(ACT_N, dtype=torch.bool, device=device)
            masked[candidates({'l': False, 'r': False, 'm': False})] = False
            online[0].masked_fill_(masked, -1e8)
            best = online.argmax(dim=1, keepdim=True)
            future = target(frames, meta)[0].gather(1, best).squeeze(1)
            expected = torch.tensor([.01, -.02], dtype=torch.float32, device=device) + .975 * future
        loss = torch.nn.functional.smooth_l1_loss(selected, expected) + .03 * (movement - controls).square().mean() + .2 * torch.nn.functional.smooth_l1_loss(observed, expected)
        if not bool(torch.isfinite(loss).item()):
            raise ValueError('实际模型计算产生非法数值')
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.)
        optimizer.step()
    model.eval()
    with torch.no_grad():
        logits, predicted, features = model(frames, meta)
        if not bool(torch.isfinite(logits).all().item()) or not bool(torch.isfinite(predicted).all().item()) or not bool(torch.isfinite(model.effect_value(features, controls)).all().item()):
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
        for device in devices:
            try:
                engine = TorchBrain(Path(folder) / '.probe_readonly', torch, device, '检测')
                validate_network(torch, engine, device)
                return True
            except Exception as error:
                sys.stderr.write(type(error).__name__ + ': ' + str(error)[:160] + '\n')
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
            torch.set_num_threads(max(1, (os.cpu_count() or 2) - 1))
            devices = [(torch.device('cpu'), 'CPU · PyTorch')]
        engine = None
        diagnostics = []
        for device, title in devices:
            try:
                engine = TorchBrain(Path(folder_name), torch, device, title)
                validate_network(torch, engine, device)
                break
            except Exception as error:
                diagnostics.append(str(error)[:120])
                engine = None
        if engine is None:
            raise RuntimeError('；'.join(diagnostics) or '没有通过计算验证的设备')
        channel.send(('ready', (engine.label, engine.steps, engine.generation, len(engine.memory))))
        while True:
            try:
                operation, payload = channel.recv()
            except EOFError:
                break
            try:
                if operation == 'choose':
                    result = engine.choose(*payload)
                elif operation == 'learn':
                    engine.learn(*payload)
                    result = None
                elif operation == 'train':
                    result = engine.train(payload, AnyStop(cancel_event, preempt_event))
                elif operation == 'begin_sleep':
                    engine.begin_sleep()
                    result = None
                elif operation == 'end_sleep':
                    result = engine.end_sleep()
                elif operation == 'sleep_progress':
                    result = engine.sleep_progress()
                elif operation == 'save':
                    engine.save(*(payload or ()))
                    result = (engine.generation, engine.slot)
                elif operation == 'sync':
                    records, steps = payload
                    with engine.save_lock:
                        engine.memory = deque(records, maxlen=REPLAY_LIMIT)
                        engine.steps = max(engine.steps, steps)
                    result = None
                elif operation == 'mark_last_done':
                    with engine.save_lock:
                        if engine.memory:
                            last = engine.memory.pop()
                            engine.memory.append((*last[:6], True, last[7], last[8]))
                    result = None
                elif operation == 'close':
                    channel.send(('ok', None))
                    break
                else:
                    raise ValueError('未识别的计算指令')
                channel.send(('ok', result))
            except Exception as error:
                channel.send(('error', type(error).__name__ + ': ' + str(error)[:320]))
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
        self.closed = False
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
            recovered = []
            for slot in (0, 1):
                pair = read_replay(folder, slot)
                if pair is not None:
                    recovered.append((pair[1], slot, pair[0]))
            if recovered:
                generation, slot, records = max(recovered, key=lambda item: item[0])
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
            raise TimeoutError('计算进程响应超时')
        try:
            return self.channel.recv()
        except (EOFError, OSError) as error:
            raise RuntimeError('计算进程意外退出') from error

    def _request(self, operation, payload=None, timeout=35):
        with self.rpc_lock:
            if self.closed or not self.process.is_alive():
                raise RuntimeError('计算进程未运行')
            self.channel.send((operation, payload))
            kind, value = self._receive(timeout)
            if kind != 'ok':
                raise RuntimeError(str(value))
            return value

    def choose(self, ob, meta, held):
        self.inference_pending.set()
        self.train_preempt.set()
        try:
            return self._request('choose', (ob, meta, held), timeout=15)
        finally:
            self.inference_pending.clear()
            self.train_preempt.clear()

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl):
        data = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl))
        self._request('learn', data, timeout=15)
        with self.save_lock:
            self.memory.append(data)
            self.steps += 1

    def train(self, count, stop):
        if stop.is_set() or self.train_cancel.is_set() or self.inference_pending.is_set() or self.train_preempt.is_set():
            return 0
        if not self.rpc_lock.acquire(blocking=False):
            return 0
        try:
            if self.inference_pending.is_set() or self.train_preempt.is_set():
                return 0
            return self._request('train', min(count, 4), timeout=45)
        finally:
            self.rpc_lock.release()

    def cancel_train(self):
        self.train_cancel.set()

    def reset_train_cancel(self):
        self.train_cancel.clear()

    def begin_sleep(self):
        self.train_cancel.clear()
        self._request('begin_sleep')

    def end_sleep(self):
        return self._request('end_sleep')

    def sleep_progress(self):
        return self._request('sleep_progress')

    def mark_last_done(self):
        with self.save_lock:
            if self.memory:
                last = self.memory.pop()
                self.memory.append((*last[:6], True, last[7], last[8]))
        self._request('mark_last_done')

    def sync(self, records, steps):
        entries = list(records)[-REPLAY_LIMIT:]
        count = max(int(steps), len(entries))
        self._request('sync', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def checkpoint(self):
        self.save()

    def save(self):
        with self.checkpoint_lock:
            generation, slot = self._request('save', (max(self.generation, self.latest_replay_generation), self.slot), timeout=100)
            self.generation, self.latest_replay_generation, self.slot = generation, generation, slot

    def close(self):
        if self.closed:
            return
        self.closed = True
        self.train_cancel.set()
        self.train_preempt.set()
        try:
            if self.process.is_alive():
                try:
                    self.channel.send(('close', None))
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
        self.last_capture_ms = 0.
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
        self.last_press = {'l': 0., 'r': 0., 'm': 0.}
        self.last_ai_cursor = None
        self.scroll_log = deque(maxlen=24)
        try:
            windows_capture = importlib.import_module('windows_capture')
            self.wgc = windows_capture.WindowsCapture(window_hwnd=self.hwnd, cursor_capture=False, draw_border=False, minimum_update_interval=40)
            @self.wgc.event
            def on_frame_arrived(frame, capture_control):
                with self.wgc_lock:
                    self.wgc_frame = frame.frame_buffer.copy()
                    self.wgc_stamp = time.monotonic()
            @self.wgc.event
            def on_closed():
                with self.wgc_lock:
                    self.wgc_frame = None
                    self.wgc_stamp = 0.
            self.wgc_control = self.wgc.start_free_threaded()
        except Exception:
            self.wgc = None
            self.wgc_control = None
        self.dark_frames = 0

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

    def capture(self, x, y, w, h):
        if self.wgc is not None:
            try:
                with self.wgc_lock:
                    image = self.wgc_frame
                    stamp = self.wgc_stamp
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
                                return sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes()
            except Exception:
                pass
        if self.grabber is not None and self.grabber_errors < 3:
            try:
                image = self.grabber.grab(region=(x, y, x + w, y + h), new_frame_only=True)
                if image is not None and len(image.shape) == 3 and image.shape[2] >= 3:
                    import numpy as np
                    ys = np.linspace(0, image.shape[0] - 1, VIS_H).astype(np.intp)
                    xs = np.linspace(0, image.shape[1] - 1, VIS_W).astype(np.intp)
                    sample = image[ys[:, None], xs[None, :], :3]
                    self.grabber_errors = 0
                    return sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes()
            except Exception:
                self.grabber_errors += 1
        if not g.StretchBlt(self.mem, 0, 0, VIS_W, VIS_H, self.src, x, y, w, h, 0x00CC0020):
            raise OSError('画面获取失败')
        raw = ctypes.string_at(self.ptr, PIXELS * 4)
        return raw[2::4] + raw[1::4] + raw[0::4]

    def image(self, region):
        capture_start = time.monotonic()
        x, y, w, h = region
        overview = self.capture(x, y, w, h)
        px, py = self.cursor()
        zoom_w = max(48, min(w, int(w * .22)))
        zoom_h = max(32, min(h, int(h * .22)))
        crop_x = max(x, min(x + w - zoom_w, px - zoom_w // 2))
        crop_y = max(y, min(y + h - zoom_h, py - zoom_h // 2))
        result = overview + self.capture(crop_x, crop_y, zoom_w, zoom_h)
        self.dark_frames = self.dark_frames + 1 if max(result) <= 2 else 0
        self.last_capture_ms = (time.monotonic() - capture_start) * 1000
        return result

    def safe(self, region, stop, require_pointer=True):
        if stop.is_set():
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
                now = time.monotonic()
                if now - self.last_press[name] < max(.08, u.GetDoubleClickTime() / 4000):
                    return False
                self.last_press[name] = now
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
                self.hold_since.pop(name, None)
            return True

    def quick_release(self):
        with self.io_lock:
            for name, flag in (('l', 4), ('r', 16), ('m', 64)):
                if self.down.get(name, False):
                    try:
                        send_mouse(flag)
                        self.down[name] = False
                        self.hold_since.pop(name, None)
                    except OSError:
                        pass
            self.velocity = (0., 0.)

    def release(self):
        self.quick_release()

    def act(self, ctrl, region, stop, dt):
        with self.io_lock:
            self.safe(region, stop)
            x, y, w, h = region
            px, py = self.cursor()
            if self.last_ai_cursor is not None and math.hypot(px - self.last_ai_cursor[0], py - self.last_ai_cursor[1]) > 10:
                raise RuntimeError('检测到人工移动鼠标，AI 已停止')
            vx, vy, speed, l, r, m, wheel, duration = ctrl
            dt = max(.015, min(.16, dt))
            magnitude = max(.0, min(1., speed)) * MAX_SPEED
            norm = math.hypot(vx, vy)
            ux, uy = ((vx / norm, vy / norm) if norm > .001 else (0., 0.))
            desired = (ux * magnitude, uy * magnitude)
            smooth = .47
            velocity = (self.velocity[0] * (1 - smooth) + desired[0] * smooth, self.velocity[1] * (1 - smooth) + desired[1] * smooth)
            if not magnitude:
                velocity = (0., 0.)
            nx = max(x + 3, min(x + w - 4, round(px + velocity[0] * dt)))
            ny = max(y + 3, min(y + h - 4, round(py + velocity[1] * dt)))
            self.safe(region, stop)
            if stop.is_set():
                raise InterruptedError('键盘急停')
            if (nx, ny) != (px, py) and not u.SetCursorPos(nx, ny):
                raise RuntimeError('鼠标移动失败')
            self.safe(region, stop)
            ex, ey = self.cursor()
            dx, dy = ex - px, ey - py
            self.last_ai_cursor = (ex, ey)
            self.velocity = (dx / dt, dy / dt)
            switches = []
            blocked = False
            now = time.monotonic()
            for key, since in list(self.hold_since.items()):
                if now - since > (2.5 if key == 'l' else .9) and self.button(key, False, stop, region):
                    switches.append(key + '-')
            for name, target in zip(('l', 'r', 'm'), (l, r, m)):
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
                limit = max(2, int(1. / max(.04, dt)))
                if now - self.last_scroll >= cadence and len(self.scroll_log) < limit:
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
                action = (23 if delta > 0 else 24) if abs(delta) == 120 else (25 if delta > 0 else 26)
            elif dx or dy:
                angle = math.atan2(dy, dx) % (2 * math.pi)
                sector = int(round(angle / (math.pi / 4))) % 8
                action = 1 + sector + (8 if math.hypot(dx, dy) / dt > 420 else 0)
            else:
                action = 0
            real_speed = min(1., math.hypot(dx, dy) / (dt * MAX_SPEED))
            distance = math.hypot(dx, dy)
            executed = [dx / distance if distance else 0., dy / distance if distance else 0., real_speed, 0., 0., 0., max(-1., min(1., delta / 120 * min(1., .075 / max(.015, dt)))), max(0., min(1., (dt - .025) / .115))]
            for switch in switches:
                executed[{'l': 3, 'r': 4, 'm': 5}[switch[0]]] = 1. if switch[1] == '+' else -1.
            changed = bool(dx or dy or switches or delta)
            requested = bool(magnitude or abs(wheel) > .08 or any((v > .5 and not self.down[k]) or (v < -.5 and self.down[k]) for k, v in zip(('l', 'r', 'm'), (l, r, m))))
            return {'action': action, 'ctrl': tuple(executed), 'scroll': delta, 'switches': tuple(switches), 'blocked': blocked or (requested and not changed), 'changed': changed, 'moved': distance}

    def close(self):
        self.release()
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
    target = folder / ('.runtime_' + backend)
    target.mkdir(parents=True, exist_ok=True)
    temp = folder / '.install_tmp'
    temp.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['TMP'] = str(temp)
    env['TEMP'] = str(temp)
    env['TMPDIR'] = str(temp)
    env['PIP_CACHE_DIR'] = str(temp / 'cache')
    report('自动匹配并配置 ' + backend + ' 计算组件…')
    cmd = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', '--no-cache-dir', '--upgrade', '--target', str(target)] + list(args)
    creation = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
    try:
        with open(temp / 'install.log', 'wb') as log:
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
                    return False
                time.sleep(.15)
            if proc.returncode == 0:
                return True
        lines = (temp / 'install.log').read_text(encoding='utf-8', errors='replace').strip().splitlines()
        report(backend + ' 安装失败' + ('：' + lines[-1][:150] if lines else ''))
        return False
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report(backend + ' 配置异常：' + str(error)[:125])
        return False
    finally:
        shutil.rmtree(temp, ignore_errors=True)


def available_cuda_wheels(driver):
    versions = {'cu118', 'cu126', 'cu128', 'cu130'}
    try:
        with urllib.request.urlopen('https://download.pytorch.org/whl/', timeout=6) as response:
            listing = response.read(500000).decode('utf-8', errors='replace')
        versions.update('cu' + value for value in re.findall(r'(?i)\bcu(\d{3})\b', listing))
    except (OSError, ValueError, TimeoutError):
        pass
    if driver is not None:
        major, minor = driver
        versions.add(f'cu{major}{minor}')
    def version(wheel):
        code = wheel[2:]
        return (int(code[:-1]), int(code[-1]))
    eligible = [wheel for wheel in versions if driver is None or version(wheel) <= driver]
    return sorted(eligible, key=version, reverse=True)


def load_brain(folder, report, cancel):
    folder.mkdir(parents=True, exist_ok=True)
    cache = folder / '.cache'
    cache.mkdir(parents=True, exist_ok=True)
    for key in ('TEMP', 'TMP', 'TMPDIR', 'XDG_CACHE_HOME', 'TORCH_HOME', 'CUDA_CACHE_PATH', 'TORCHINDUCTOR_CACHE_DIR', 'TRITON_CACHE_DIR'):
        os.environ[key] = str(cache)
    gpus = detect_gpu()
    nvidia = any('nvidia' in name.lower() for name in gpus)
    cuda_runtimes = sorted(folder.glob('.runtime_cuda_cu*'), reverse=True)
    directml_runtime = folder / '.runtime_directml'
    cpu_runtime = folder / '.runtime_cpu'
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
            report('正在匹配 NVIDIA 驱动与 CUDA 计算组件…')
            driver = None
            try:
                result = subprocess.run(['nvidia-smi'], text=True, capture_output=True, timeout=9, creationflags=subprocess.CREATE_NO_WINDOW)
                match = re.search(r'CUDA Version:\s*(\d+)\.(\d+)', result.stdout)
                if match:
                    driver = (int(match.group(1)), int(match.group(2)))
            except (OSError, subprocess.SubprocessError):
                pass
            for wheel in available_cuda_wheels(driver):
                if cancel.is_set():
                    break
                runtime = folder / ('.runtime_cuda_' + wheel)
                if runtime.exists() and (runtime / 'torch').exists():
                    ready = launch(runtime, 'cuda')
                    if ready is not None:
                        return ready
                    continue
                if install_package(folder, ['--index-url', 'https://download.pytorch.org/whl/' + wheel, 'torch'], report, cancel, 'cuda_' + wheel):
                    ready = launch(runtime, 'cuda')
                    if ready is not None:
                        return ready
        for runtime in ([directml_runtime, None] if directml_runtime.exists() else [None]):
            ready = launch(runtime, 'directml')
            if ready is not None:
                return ready
        if gpus and not cancel.is_set() and not (directml_runtime / 'torch_directml').exists():
            if install_package(folder, ['torch-directml'], report, cancel, 'directml'):
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
        report('已识别显卡：' + '、'.join(gpus[:3]) + '；CUDA / DirectML 计算自检未通过，当前改用 CPU，后续可自动重试')
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
        self.folder = Path(__file__).resolve().parent
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
        self.keyboard_ready = threading.Event()
        self.control_heartbeat = 0.
        self.watchdog_limit = 3.
        self.close_started = 0.
        self.saver = None
        self.last_checkpoint = 0.
        self.next_backend_retry = 0.
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
        self.build()
        self.root.protocol('WM_DELETE_WINDOW', self.close)
        self.root.after(90, self.pump)
        self.root.after(400, self.refresh)
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
                self.control_details.set(val)
            elif kind == 'done':
                if self.mode != 'closed' and val == self.mode:
                    self.mode = 'idle'
            elif kind == 'error':
                self.status.set('发生问题：' + val)
        if self.mode == 'control' and (not self.keyboard_ready.is_set() or not self.wheel_hook_ready):
            self.emergency_stop('输入安全钩子不可用，已停止鼠标控制')
        if not self.exit_stop.is_set():
            self.root.after(90, self.pump)

    def refresh(self):
        if os.name != 'nt':
            self.status.set('当前版本支持 Windows 10/11 桌面窗口')
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
        if self.mode != 'closed':
            self.root.after(3000, self.refresh)

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
            self.status.set('已切换学习数据文件夹；旧计算资源已释放')

    def load(self, task_stop):
        if self.brain is not None and self.brain_folder == self.folder:
            retry = time.monotonic() >= self.next_backend_retry and bool(detect_gpu()) and not self.brain.accelerated
            if not retry:
                return
            self.post('status', '正在重新检查显卡驱动与计算后端…')
            self.brain.save()
        cancel = AnyStop(self.exit_stop, task_stop)
        if cancel.is_set():
            return
        self.post('status', '检测硬件并准备学习模型…')
        brain = load_brain(self.folder, lambda msg: self.post('status', msg), cancel)
        ensure_capture(self.folder, lambda msg: self.post('status', msg), cancel)
        if cancel.is_set():
            if isinstance(brain, RemoteBrain):
                brain.close()
            return
        previous_brain = self.brain
        if previous_brain is not None and brain is not previous_brain:
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
        self.brain_folder = self.folder
        if previous_brain is not brain and isinstance(previous_brain, RemoteBrain):
            previous_brain.close()
        self.next_backend_retry = time.monotonic() + 600 if not brain.accelerated else 0.
        self.post('backend', self.brain.label)

    def recover_learning_backend(self, error):
        if self.active_io is not None:
            self.active_io.quick_release()
        self.online_stop.set()
        if self.online_worker is not None and self.online_worker.is_alive() and self.online_worker is not threading.current_thread():
            self.online_worker.join(timeout=5)
            if self.online_worker.is_alive():
                raise RuntimeError('计算进程未能及时停止训练，已中止本轮鼠标控制')
        if self.saver is not None and self.saver.is_alive():
            self.saver.join(timeout=8)
            if self.saver.is_alive():
                raise RuntimeError('模型保存仍在进行，本轮操作已停止')
        self.next_backend_retry = time.monotonic() + 600
        self.post('status', '计算状态异常，自动切换兼容学习模式：' + str(error)[:70])
        former = self.brain
        backup = None
        if isinstance(former, RemoteBrain):
            try:
                former.close()
                backup = RemoteBrain(self.folder, None, 'cpu')
            except Exception:
                backup = None
        if backup is None:
            backup = LiteBrain(self.folder)
        if former is not None:
            with former.save_lock:
                recovered = list(former.memory)
                steps = former.steps
            if isinstance(backup, RemoteBrain):
                try:
                    backup.sync(recovered, steps)
                except Exception:
                    backup.close()
                    backup = LiteBrain(self.folder)
            if not isinstance(backup, RemoteBrain):
                backup.restore_experience(recovered, steps)
        self.brain = backup
        self.post('backend', backup.label)

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
                active.quick_release()
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
                    count = len(brain.memory)
                if count >= 32:
                    brain.train(min(4, max(1, int(math.sqrt(count) / 8))), self.online_stop)
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
        if os.name != 'nt':
            self.status.set('当前版本需要 Windows 10/11')
            return
        if not self.keyboard_ready.wait(.3):
            self.status.set('键盘与鼠标安全钩子未就绪，已阻止控制启动')
            return
        if self.mode != 'idle' or (self.worker is not None and self.worker.is_alive()):
            self.status.set('上一个操作尚未结束')
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None:
            self.status.set('请先选择一个有效窗口')
            return
        self.control_stop.clear()
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
                elif self.mouse_monitor_armed.is_set() and self.control_heartbeat > 0 and time.monotonic() - self.control_heartbeat > self.watchdog_limit:
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
                        active.quick_release()
                    except OSError:
                        pass
            else:
                canceled = False
        active = self.active_io
        if active is not None:
            try:
                active.quick_release()
            except OSError:
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
        vx = (px - prior[0]) / max(.02, dt)
        vy = (py - prior[1]) / max(.02, dt)
        speed = min(1, math.hypot(vx, vy) / 1000)
        return [math.sin(now / 60), math.cos(now / 60), math.sin(now / 3600), math.cos(now / 3600),
                min(1., max(0., (px - x) / max(1, w))), min(1., max(0., (py - y) / max(1, h))),
                max(-1., min(1., vx / 850)), max(-1., min(1., vy / 850)), speed,
                float(held['l']), float(held['r']), float(held['m']),
                max(-1., min(1., scroll / 240)), min(1., abs(scroll) / (2200 * max(.02, dt))),
                min(1., dt * 10), min(1., w / max(1, h) / 4), min(1., diff * 3),
                float(scroll != 0)]

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
            prev_pos = io.cursor()
            prev_dt = .075
            prev_change = 0.
            last_scroll = 0
            last_tick = time.monotonic()
            self.last_checkpoint = last_tick
            novelty_count = 0
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
                    prev_pos = io.cursor()
                    prev_dt = .075
                    prev_change = 0.
                    self.post('status', '窗口区域已变化，正在按新位置和尺寸继续控制')
                io.safe(region, stop)
                frame = io.image(region)
                capture_ms = io.last_capture_ms
                mouse = io.cursor()
                held = io.keys()
                scroll = self.wheel_delta() if self.wheel_hook_ready else last_scroll
                meta = self.create_meta(start, region, mouse, prev_pos, held, scroll, prev_dt, prev_change)
                infer_start = time.monotonic()
                try:
                    action, ctrl = self.brain.choose(frame, meta, io.down)
                except Exception as ex:
                    self.recover_learning_backend(ex)
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
                if io.dark_frames > 20:
                    self.post('status', '检测到持续黑屏，暂停操作；请检查窗口是否允许捕获')
                    raise RuntimeError('目标窗口画面持续黑屏，已停止控制以避免误操作')
                duration = .025 + .115 * max(0., min(1., ctrl[7]))
                outcome = io.act(ctrl, region, stop, duration)
                outcome['requested_action'] = action
                if self.control_stop.wait(.037) or stop.is_set():
                    break
                if io.region() != region:
                    updated = io.region()
                    if updated is None or not io.foreground():
                        raise RuntimeError('窗口区域已失效，停止控制')
                    io.release()
                    region = updated
                    io.prepare_cursor(region, stop)
                    prev_frame = io.image(region)
                    prev_pos = io.cursor()
                    prev_dt = .075
                    prev_change = 0.
                    continue
                io.safe(region, stop)
                nxt = io.image(region)
                capture_times.append(capture_ms + io.last_capture_ms)
                frame_times.append(tick_interval)
                new_mouse = io.cursor()
                reward, change, novel = feedback.assess(frame, nxt, prev_frame, outcome, new_mouse, region)
                actual_dt = max(.01, min(2., time.monotonic() - start))
                new_scroll = self.wheel_delta() if self.wheel_hook_ready else outcome['scroll']
                nmeta = self.create_meta(time.monotonic(), region, new_mouse, mouse, io.keys(), new_scroll, actual_dt, change)
                try:
                    self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'])
                except Exception as error:
                    self.recover_learning_backend(error)
                    self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'])
                last_experience = ticks
                ticks += 1
                self.iterations += 1
                novelty_count += int(novel)
                if ticks % 12 == 0:
                    executed = outcome['ctrl']
                    buttons = io.keys()
                    self.post('control', f'方向 ({executed[0]:+.2f}, {executed[1]:+.2f}) · 速度 {executed[2] * MAX_SPEED:.0f}px/s · 左/右/中键 {int(buttons["l"])}/{int(buttons["r"])}/{int(buttons["m"])} · 滚轮指令 {ctrl[6]:+.2f} · 滚轮输出 {outcome["scroll"]:+d} · 决策 {action} / 实际 {outcome["action"]}')
                if ticks % 32 == 0:
                    def p95(samples):
                        ordered = sorted(samples)
                        return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * .95))] if ordered else 0.
                    fps = len(frame_times) / max(.001, sum(frame_times))
                    self.post('stats', f'经验 {len(self.brain.memory)} · 操作 {self.iterations} · 画面响应 {feedback.effects}/{feedback.total} · 新颖反馈 {novelty_count} · 无效 {feedback.blocks} · FPS {fps:.1f} · 推理P95 {p95(infer_times):.0f}ms · 采集P95 {p95(capture_times):.0f}ms')
                if time.monotonic() - self.last_checkpoint > 32:
                    self.last_checkpoint = time.monotonic()
                    self.schedule_checkpoint()
                prev_frame = frame
                prev_pos = mouse
                prev_change = change
                prev_dt = actual_dt
                last_scroll = outcome['scroll']
                stop_delay = max(0., duration - (time.monotonic() - start))
                if self.control_stop.wait(stop_delay):
                    break
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
                    io.release()
                except Exception:
                    pass
                self.active_io = None
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
                                self.brain.memory.append((*last[:6], True, last[7], last[8]))
                    if self.saver is not None and self.saver.is_alive():
                        self.saver.join(timeout=8)
                    if self.saver is None or not self.saver.is_alive():
                        self.brain.save()
                    else:
                        self.post('error', '已有保存任务仍在执行，避免重复保存写入')
                except Exception as ex:
                    self.post('error', '模型保存失败：' + str(ex)[:130])
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
            if self.saver is not None and self.saver.is_alive():
                self.saver.join(timeout=8)
                if self.saver.is_alive():
                    raise RuntimeError('模型正在保存，已取消本次睡眠训练')
            if self.exit_stop.is_set():
                return
            self.load(self.sleep_stop)
            if self.sleep_stop.is_set() or self.exit_stop.is_set():
                return
            mem = len(self.brain.memory)
            if mem == 0:
                self.post('status', '尚无交互经验；先点击绿色按钮让 AI 感知并探索窗口')
                return
            self.post('status', f'AI 睡眠中：正在巩固 {mem} 条交互经验…')
            if hasattr(self.brain, 'begin_sleep'):
                self.brain.begin_sleep()
            start = time.monotonic()
            steps = 0
            ceiling = min(2500, max(100, mem * 3))
            best_loss = None
            stalled = 0
            next_check = 48
            while steps < ceiling and time.monotonic() - start < 45 and not self.sleep_stop.is_set() and not self.exit_stop.is_set():
                try:
                    n = self.brain.train(min(12, ceiling - steps), self.sleep_stop)
                except Exception as ex:
                    self.recover_learning_backend(ex)
                    n = self.brain.train(min(12, ceiling - steps), self.sleep_stop)
                steps += n
                if n == 0:
                    break
                if steps % 60 < 12:
                    self.post('stats', f'经历 {mem} 帧 · 睡眠巩固 {steps}/{ceiling} 步')
                if steps >= next_check and hasattr(self.brain, 'sleep_progress'):
                    next_check = steps + 48
                    loss = self.brain.sleep_progress()
                    if loss is not None:
                        if best_loss is None or loss < best_loss - max(1e-6, abs(best_loss) * .002):
                            best_loss = loss
                            stalled = 0
                        else:
                            stalled += 1
                        if stalled >= 5:
                            break
            result = self.brain.end_sleep() if hasattr(self.brain, 'end_sleep') else None
            self.brain.save()
            interrupted = self.sleep_stop.is_set() or self.exit_stop.is_set()
            prefix = '提前唤醒' if interrupted else '自然唤醒'
            positive = sum(row[5] > .004 for row in self.brain.memory)
            rate = 100 * positive / max(1, len(self.brain.memory))
            behavior = ''
            if result is not None and len(result) >= 5 and result[3] is not None and result[4] is not None:
                behavior = f'，留出经验的反馈偏好 {100 * result[3]:.0f}% → {100 * result[4]:.0f}%'
            if result is not None and result[0] is False:
                self.post('status', f'AI {prefix}；离线验证退化，已回滚训练（{steps} 步）{behavior}；历史正反馈 {rate:.1f}%')
            elif result is not None and result[0] is None:
                self.post('status', f'AI {prefix}；没有验证到可靠提升，已保留原模型（{steps} 步）{behavior}；实际能力待验证')
            elif result is not None:
                self.post('status', f'AI {prefix}；保留最佳训练结果（{steps} 步），离线误差 {result[1]:.4f} → {result[2]:.4f}{behavior}；实际能力待验证')
            else:
                self.post('status', f'AI {prefix}；完成 {steps} 步，历史正反馈 {rate:.1f}%；没有足够的独立验证样本')
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
        self.close_started = time.monotonic()
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

    def finish_close(self):
        busy = any(thread is not None and thread.is_alive() for thread in (self.worker, self.key_thread, self.safety_thread, self.saver, self.online_worker))
        if busy and time.monotonic() - self.close_started < 12.:
            self.root.after(80, self.finish_close)
            return
        if self.active_io is not None:
            try:
                self.active_io.quick_release()
            except Exception:
                pass
        if isinstance(self.brain, RemoteBrain):
            try:
                self.brain.close()
            except Exception:
                pass
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
