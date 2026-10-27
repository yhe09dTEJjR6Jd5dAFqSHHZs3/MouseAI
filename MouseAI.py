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
import urllib.parse
import html
import multiprocessing as mp
import atexit
import tempfile
import sqlite3
import zlib
import heapq
from pathlib import Path
from collections import deque, Counter
from bisect import bisect_left
from functools import lru_cache
import tkinter as tk
from tkinter import ttk, filedialog

VIS_W = 128
VIS_H = 72
PIXELS = VIS_W * VIS_H
CHANNELS = 3
VIS_N = PIXELS * CHANNELS * 2
CTRL_N = 8
META_N = 20
AI_INPUT_MARK = int.from_bytes(os.urandom(ctypes.sizeof(ctypes.c_size_t)), 'little') | 1
CHILD_PROCESSES = set()
CHILD_LOCK = threading.RLock()


def managed_process(*args, **kwargs):
    process = subprocess.Popen(*args, **kwargs)
    with CHILD_LOCK:
        CHILD_PROCESSES.add(process)
    return process


def release_process(process):
    with CHILD_LOCK:
        CHILD_PROCESSES.discard(process)


def stop_process_tree(process):
    if process is None:
        return
    try:
        if process.poll() is None:
            if os.name == 'nt':
                try:
                    subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=3, creationflags=subprocess.CREATE_NO_WINDOW)
                except (OSError, subprocess.SubprocessError):
                    pass
            if process.poll() is None:
                process.kill()
        process.wait(timeout=2)
    except (OSError, subprocess.SubprocessError):
        pass
    finally:
        release_process(process)


def stop_all_processes():
    with CHILD_LOCK:
        children = list(CHILD_PROCESSES)
    for process in children:
        stop_process_tree(process)
MAX_REPLAY_RECORDS = max(512, int(math.sqrt(max(1, (os.cpu_count() or 1) * 1024 * 1024))))
REPLAY_MAGIC = b'MOUSEAI8'
REPLAY_PACK = struct.Struct('<BBf?ff?' + 'f' * (META_N * 2 + CTRL_N * 2))

def available_memory():
    if os.name == 'nt':
        try:
            class MEMORYSTATUSEX(ctypes.Structure):
                _fields_ = [('dwLength', ctypes.c_ulong), ('dwMemoryLoad', ctypes.c_ulong), ('ullTotalPhys', ctypes.c_ulonglong), ('ullAvailPhys', ctypes.c_ulonglong), ('ullTotalPageFile', ctypes.c_ulonglong), ('ullAvailPageFile', ctypes.c_ulonglong), ('ullTotalVirtual', ctypes.c_ulonglong), ('ullAvailVirtual', ctypes.c_ulonglong), ('ullAvailExtendedVirtual', ctypes.c_ulonglong)]
            state = MEMORYSTATUSEX()
            state.dwLength = ctypes.sizeof(state)
            if ctypes.WinDLL('kernel32').GlobalMemoryStatusEx(ctypes.byref(state)):
                return int(state.ullAvailPhys)
        except (OSError, AttributeError, ValueError):
            pass
    elif hasattr(os, 'sysconf'):
        try:
            return int(os.sysconf('SC_AVPHYS_PAGES') * os.sysconf('SC_PAGE_SIZE'))
        except (OSError, ValueError):
            pass
    return 0


def replay_capacity():
    free = available_memory()
    if not free:
        return MAX_REPLAY_RECORDS
    sample_size = VIS_N * 2 + REPLAY_PACK.size
    headroom = free / max(1., sample_size)
    return max(64, MAX_REPLAY_RECORDS, int(headroom / max(8., math.log2(2. + headroom))))

REPLAY_LIMIT = replay_capacity()
ACT = [(0, 0, 0, '', 0)]
for magnitude in (.3, .7):
    for angle in range(8):
        a = angle * math.tau / 8
        ACT.append((math.cos(a), math.sin(a), magnitude, '', 0))
ACT += [(0, 0, 0, 'l+', 0), (0, 0, 0, 'l-', 0), (0, 0, 0, 'r+', 0), (0, 0, 0, 'r-', 0), (0, 0, 0, 'm+', 0), (0, 0, 0, 'm-', 0), (0, 0, 0, '', .5), (0, 0, 0, '', -.5), (0, 0, 0, '', 1.), (0, 0, 0, '', -1.)]
ACT_N = len(ACT)

atexit.register(stop_all_processes)

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


def visual_attention(observation, meta):
    if observation is None or len(observation) != VIS_N or meta is None:
        return None
    step_x = max(1, int(math.sqrt(VIS_W)))
    step_y = max(1, int(math.sqrt(VIS_H)))
    points = []
    for y in range(step_y, VIS_H - step_y, step_y):
        for x in range(step_x, VIS_W - step_x, step_x):
            i = y * VIS_W + x
            j = i + step_x
            k = i + step_y * VIS_W
            contrast = sum(abs(observation[c * PIXELS + i] - observation[c * PIXELS + j]) + abs(observation[c * PIXELS + i] - observation[c * PIXELS + k]) for c in range(CHANNELS))
            points.append(((x + .5) / VIS_W, (y + .5) / VIS_H, contrast))
    if not points:
        return None
    mx, my = float(meta[4]), float(meta[5])
    observed = [part[2] for part in points]
    typical = sorted(observed)[len(observed) // 2]
    spread = sum(abs(v - typical) for v in observed) / len(observed)
    salient = [(x, y, max(0., value - typical) / max(1., spread)) for x, y, value in points]
    if not any(value > 0. for _, _, value in salient) and typical > 0.:
        salient = [(x, y, value / typical) for x, y, value in points]
    total = sum(value for _, _, value in salient)
    if total <= 0.:
        return None
    weights = [value / (1. + math.hypot(x - mx, y - my)) for x, y, value in salient]
    selected = random.choices(salient, weights=weights, k=1)[0]
    nearest = min(salient, key=lambda item: math.hypot(item[0] - mx, item[1] - my))
    mean_strength = total / len(salient)
    local = nearest[2] / max(1., mean_strength)
    dx, dy = selected[0] - mx, selected[1] - my
    return dx, dy, min(1., local / (1. + local)), min(1., math.hypot(dx, dy))


def action_caution(action, experience):
    button = ACT[action][3]
    wheel = ACT[action][4]
    if button.endswith('-'):
        return -1.
    if button:
        return (2. if button[0] != 'l' else 1.) * (1. - experience)
    if wheel:
        return (1. - experience) * abs(wheel)
    return 0.


def experienced_fraction(steps):
    steps = max(0, int(steps))
    return steps / (steps + math.sqrt(REPLAY_LIMIT))


def careful_choice(values, allowed, steps):
    if not allowed:
        return 0
    experience = experienced_fraction(steps)
    mean = sum(values[a] for a in allowed) / len(allowed)
    spread = math.sqrt(sum((values[a] - mean) ** 2 for a in allowed) / len(allowed))
    return max(allowed, key=lambda a: values[a] - spread * action_caution(a, experience))


def explore_action(allowed, meta=None, steps=0, observation=None, targets=None):
    if not allowed:
        return 0
    if meta is None:
        return random.choice(allowed)
    change = max(0., float(meta[16]))
    held = sum(float(meta[i]) > .5 for i in (9, 10, 11))
    focus = visual_attention(observation, meta)
    exposure = experienced_fraction(steps)
    guided = None
    if targets:
        mx, my = float(meta[4]), float(meta[5])
        nearby = sorted(targets, key=lambda point: math.hypot(point[0] - mx, point[1] - my))
        best = nearby[:max(1, int(math.sqrt(len(nearby))))]
        tx, ty, kind = random.choice(best)
        guided = (tx - mx, ty - my, int(kind))
    scores = []
    for action in allowed:
        vx, vy, speed, button, wheel = ACT[action]
        activity = abs(speed) + abs(wheel) + bool(button)
        penalty = (1. + held) if button and button.endswith('+') else 1.
        weight = (1. + change) / (1. + activity * penalty)
        if button.endswith('-'):
            weight *= 1. + 1. / max(exposure, 1. / (1. + REPLAY_LIMIT))
        elif button == 'l+':
            weight *= exposure
        elif button.endswith('+'):
            weight *= exposure * exposure
        elif wheel:
            weight *= exposure
        if focus is None and guided is None and button.endswith('+'):
            weight *= exposure
        if focus is not None:
            dx, dy, local, distance = focus
            if speed:
                direction = (vx * dx + vy * dy) / max(1e-8, math.hypot(dx, dy))
                weight *= math.exp(max(-1., min(1., direction)) * (1. + distance))
            elif button == 'l+':
                weight *= local / (1. + distance * (1. + local))
            elif button.endswith('+'):
                weight *= local / (1. + distance + held)
        if guided is not None:
            dx, dy, kind = guided
            distance = math.hypot(dx, dy)
            if speed and distance > 0.:
                alignment = (vx * dx + vy * dy) / max(1e-8, distance)
                weight *= math.exp(max(-1., min(1., alignment)) * (2. + distance))
            elif button == 'l+':
                radius = 2. / max(1., math.sqrt(VIS_W * VIS_H))
                if distance < radius * 2.:
                    weight = max(weight, 1. + kind / (1. + distance / radius))
            elif button.endswith('+'):
                weight *= exposure
        scores.append(max(0., weight))
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
    movement = sorted({value[2] for value in ACT if value[2] > 0.})
    wheels = sorted({abs(value[4]) for value in ACT if value[4]})
    if 1 <= action < 17:
        directions = sorted({math.atan2(value[1], value[0]) % math.tau for value in ACT if value[2] > 0.})
        span = math.tau / max(1, len(directions))
        angle = math.atan2(ctrl[1], ctrl[0]) + random.uniform(-span / 2., span / 2.)
        ctrl[0], ctrl[1] = math.cos(angle), math.sin(angle)
        mid = sum(movement) / len(movement)
        lower, upper = (0., mid) if ctrl[2] <= mid else (mid, 1.)
        ctrl[2] = random.uniform(max(lower, math.nextafter(0., 1.)), upper)
    elif action >= 23 and wheels:
        mid = sum(wheels) / len(wheels)
        lower, upper = (0., mid) if abs(ctrl[6]) <= mid else (mid, 1.)
        ctrl[6] = math.copysign(random.uniform(max(lower, math.nextafter(0., 1.)), upper), ctrl[6])
    ctrl[7] = random.betavariate(2., 2.)
    return normalize_control(ctrl)

def sleep_split(records):
    held_out = [i for i, row in enumerate(records) if row[12]]
    if not held_out:
        return None
    runs = []
    first = last = held_out[0]
    for index in held_out[1:]:
        if index != last + 1 or records[last][6]:
            runs.append((first, last))
            first = index
        last = index
    runs.append((first, last))
    if len(runs) < 2:
        return None
    typical = sorted(end - start + 1 for start, end in runs)[len(runs) // 2]
    guard = max(1, int(math.sqrt(typical)))
    excluded = bytearray(len(records))
    for start, end in runs:
        left, right = max(0, start - guard), min(len(records), end + guard + 1)
        excluded[left:right] = b'\x01' * (right - left)
    training = [row for i, row in enumerate(records) if not excluded[i] and not row[12]]
    audit_runs = max(1, len(runs) // 3)
    cutoff = runs[-audit_runs][0]
    validation = [records[i] for i in held_out if i < cutoff]
    audit = [records[i] for i in held_out if i >= cutoff]
    minimum = max(4, int(math.log2(2. + len(records))))
    if min(len(training), len(validation), len(audit)) < minimum:
        return None
    return training, validation, audit


class ReplaySampler:
    def __init__(self, records, indices):
        self.indices = list(indices)
        scenes = [session_signature(records[i][0]) for i in self.indices]
        counts = Counter(scenes)
        influence = [abs(records[i][5]) + abs(1. - records[i][11]) for i in self.indices]
        typical = sum(influence) / max(1, len(influence))
        self.cumulative = []
        total = 0.
        for scene, importance in zip(scenes, influence):
            familiarity = counts[scene]
            total += math.sqrt(1. + importance / max(1e-8, typical)) / math.sqrt(familiarity)
            self.cumulative.append(total)
        self.total = total

    def draw(self, count):
        size = min(max(0, int(count)), len(self.indices))
        if not size:
            return []
        result = set(random.sample(self.indices, size - size // 2))
        attempts = 0
        while len(result) < size and attempts < size * 8:
            chosen = bisect_left(self.cumulative, random.random() * self.total)
            result.add(self.indices[min(chosen, len(self.indices) - 1)])
            attempts += 1
        if len(result) < size:
            result.update(random.sample([i for i in self.indices if i not in result], size - len(result)))
        return list(result)


def multi_step_experience(records, index):
    first = records[index]
    total = 0.
    discount = 1.
    duration = 0.
    final = first
    horizon = max(1, int(math.log2(1. + len(records))))
    for offset in range(horizon):
        position = index + offset
        if position >= len(records):
            break
        row = records[position]
        if row[12] or (offset and (final[6] or row[1][-2:] != final[4][-2:])):
            break
        total += discount * row[5]
        duration += row[7]
        discount *= .975 ** (row[7] / .075)
        final = row
        if row[6]:
            break
    return (first[0], first[1], first[2], final[3], final[4], total, final[6], duration, *first[8:])


def quarantine(path):
    if path.exists():
        try:
            os.replace(path, path.with_name(path.name + '.damaged'))
        except OSError:
            pass

_IMAGE_NUMPY = None
_IMAGE_NUMPY_CHECKED = False


@lru_cache(maxsize=16)
def coarse_image_cells(image):
    global _IMAGE_NUMPY, _IMAGE_NUMPY_CHECKED
    if len(image) != VIS_N:
        raise ValueError('状态识别画面维度不匹配')
    if not _IMAGE_NUMPY_CHECKED:
        _IMAGE_NUMPY_CHECKED = True
        try:
            _IMAGE_NUMPY = importlib.import_module('numpy')
        except ImportError:
            pass
    if _IMAGE_NUMPY is not None:
        np = _IMAGE_NUMPY
        cells = np.frombuffer(image, dtype=np.uint8).reshape(2, CHANNELS, VIS_H // 9, 9, VIS_W // 16, 16)
        return tuple(int(v) for v in (cells.sum(axis=(3, 5)) // (9 * 16)).transpose(0, 2, 3, 1).reshape(-1))
    out = []
    for scale in range(2):
        for y in range(0, VIS_H, 9):
            for x in range(0, VIS_W, 16):
                for channel in range(CHANNELS):
                    base = (scale * CHANNELS + channel) * PIXELS
                    out.append(sum(sum(image[base + (y + offset) * VIS_W + x:base + (y + offset) * VIS_W + x + 16]) for offset in range(9)) // 144)
    return tuple(out)


def session_signature(image):
    return hashlib.blake2s(bytes(coarse_image_cells(image)), digest_size=8).digest()


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
        self.trail = deque(maxlen=max(5, int(math.log2(2. + REPLAY_LIMIT))))
        self.outcome_graph = {}
        self.loop_count = 0
        self.causal_total = 0.
        self.context_effects = {}
        self.context_attempts = {}
        self.passive_context = {}
        try:
            self.numpy = importlib.import_module('numpy')
        except ImportError:
            self.numpy = None

    def reset_segment(self):
        self.sequence.clear()
        self.trail.clear()
        self.recent_states.clear()
        self.background = None
        self.variance = 0.

    def difference(self, left, right):
        if len(left) != VIS_N or len(right) != VIS_N:
            raise ValueError('画面反馈维度不匹配')
        if self.numpy is not None:
            np = self.numpy
            a = np.frombuffer(left, dtype=np.uint8).astype(np.int16)
            b = np.frombuffer(right, dtype=np.uint8).astype(np.int16)
            return float(np.abs(a - b).mean()) / 255.
        return sum(abs(a - b) for a, b in zip(left, right)) / (VIS_N * 255.)

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
        signature = session_signature(new)
        old_signature = session_signature(old)
        context = hashlib.blake2s(old_signature, digest_size=3).digest()
        idle_mean, idle_var, idle_visits = self.passive_context.get(context, (0., 0., 0))
        baseline = max(bg, noise, natural, idle_mean + math.sqrt(max(0., idle_var)))
        impact = max(0., dist - baseline)
        if not changed and not outcome['blocked']:
            passive_rate = 1. / math.sqrt(1. + idle_visits)
            idle_delta = dist - idle_mean
            self.passive_context[context] = (idle_mean + passive_rate * idle_delta, idle_var + passive_rate * (idle_delta * idle_delta - idle_var), idle_visits + 1)
            if len(self.passive_context) > REPLAY_LIMIT:
                for key in sorted(self.passive_context, key=lambda k: self.passive_context[k][2])[:max(1, len(self.passive_context) // 4)]:
                    self.passive_context.pop(key, None)
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
        limit_x = max(1. / max(1, w), float(outcome['moved']) / max(1, w))
        limit_y = max(1. / max(1, h), float(outcome['moved']) / max(1, h))
        intended_dx = float(intended[0]) * float(intended[2])
        intended_dy = float(intended[1]) * float(intended[2])
        at_edge = (intended_dx < 0. and cx <= limit_x or intended_dx > 0. and 1. - cx <= limit_x or intended_dy < 0. and cy <= limit_y or intended_dy > 0. and 1. - cy <= limit_y)
        efficacy = max(0., min(1., float(outcome.get('efficacy', 1.))))
        minimum = 1. / (VIS_N * 255.)
        signal = changed and impact > max(minimum, noise / math.sqrt(count))
        dynamics_key = (context, signature_control)
        context_motion, context_visits = self.context_effects.get(context, (0., 0))
        context_surprise = max(0., impact - context_motion) / max(minimum, impact + noise)
        repeated_attempts = self.context_attempts.get(dynamics_key, 0)
        self.context_attempts[dynamics_key] = repeated_attempts + 1
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
        reverse_visits = self.transition_frequency.get((signature, old_signature), 0)
        trajectory = tuple(self.trail)[-3:]
        multi_step = (trajectory, signature)
        trajectory_visits = self.outcome_graph.get(multi_step, 0)
        self.outcome_graph[multi_step] = trajectory_visits + 1
        if len(self.outcome_graph) > REPLAY_LIMIT:
            for key in sorted(self.outcome_graph, key=self.outcome_graph.get)[:max(1, len(self.outcome_graph) // 4)]:
                self.outcome_graph.pop(key, None)
        previous_transition_count = self.transition_frequency.get(transition, 0)
        self.transition_frequency[transition] = previous_transition_count + 1
        if len(self.transition_frequency) > REPLAY_LIMIT:
            for key in sorted(self.transition_frequency, key=self.transition_frequency.get)[:max(1, len(self.transition_frequency) // 4)]:
                self.transition_frequency.pop(key, None)
        lookback = len(self.recent_states)
        repeated_state = self.recent_states.count(signature) / max(1, lookback)
        short_cycle = any(signature == state for state in list(self.recent_states)[-min(4, lookback):])
        loop = lookback > 1 and old_signature != signature and (short_cycle or repeated_state > 1. / math.sqrt(lookback))
        multi_novelty = 1. / math.sqrt(1. + trajectory_visits)
        progress = float(signal and old_signature != signature and not loop and predictable >= surprise and context_surprise > 0.)
        transition_novelty = 1. / math.sqrt(1. + previous_transition_count)
        progress_gain = progress * agreement * efficacy * transition_novelty * multi_novelty * context_surprise / (1. + reverse_visits)
        self.stagnant = 0 if progress else self.stagnant + 1
        self.recent_states.append(signature)
        self.trail.append((old_signature, signature))
        gain = agreement * consistency * efficacy * float(signal) * multi_novelty * context_surprise + progress_gain
        penalty = (1. - efficacy) * float(any(abs(v) > .08 for v in intended[:7]))
        penalty += float(loop) * (repeated_state + 1. / math.sqrt(max(1, lookback))) * (1. + float(not signal))
        penalty += float(bool(reverse_visits) and signal) * min(1., reverse_visits / (1. + previous_transition_count + reverse_visits))
        penalty += float(changed and not signal) * min(1., self.stagnant / math.sqrt(1. + self.total))
        penalty += float(bool(outcome['blocked']))
        penalty += max(0., surprise - consistency) * agreement / math.sqrt(1. + seen)
        penalty += repetition * float(not signal and requested != 0) / math.sqrt(1. + seen)
        penalty += float(changed and not signal) * repeated_attempts / (1. + repeated_attempts)
        penalty += (1. - efficacy) * agreement
        penalty += float(at_edge) * float(outcome['moved'] > 0.)
        penalty += float(changed and dist <= baseline) * min(1., repetition + repeated_attempts / (1. + repeated_attempts))
        reward = math.tanh(gain - penalty)
        update_rate = 1. / math.sqrt(1. + seen)
        expected = prediction + update_rate * (impact - prediction)
        spread = uncertainty + update_rate * (deviation - uncertainty)
        self.dynamics[dynamics_key] = (expected, max(minimum, spread), seen + 1)
        context_rate = 1. / math.sqrt(1. + context_visits)
        self.context_effects[context] = (context_motion + context_rate * (impact - context_motion), context_visits + 1)
        if len(self.context_effects) > REPLAY_LIMIT:
            for key in sorted(self.context_effects, key=lambda k: self.context_effects[k][1])[:max(1, len(self.context_effects) // 4)]:
                self.context_effects.pop(key, None)
        if len(self.context_attempts) > REPLAY_LIMIT:
            for key in sorted(self.context_attempts, key=self.context_attempts.get)[:max(1, len(self.context_attempts) // 4)]:
                self.context_attempts.pop(key, None)
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
        self.causal_total += agreement
        self.loop_count += int(loop)
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
    headers = []
    for slot in (0, 1, 'recovery'):
        path = folder / f'experience.{slot}.gz'
        try:
            with gzip.open(path, 'rb') as source:
                head = source.read(len(REPLAY_MAGIC) + 12)
            if len(head) == len(REPLAY_MAGIC) + 12 and head.startswith(REPLAY_MAGIC):
                count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
                if 0 <= count <= max(REPLAY_LIMIT * 8, 1024) and generation > 0:
                    headers.append((generation, slot))
        except (OSError, EOFError, ValueError, struct.error):
            continue
    for generation, slot in sorted(headers, key=lambda row: (row[0], row[1] != 'recovery'), reverse=True):
        record = read_replay(folder, slot)
        if record is not None and record[1] == generation:
            yield generation, slot, record[0]


def newest_replay(folder):
    return next(replay_sources(folder), None)


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



class LifelongMemory:
    def __init__(self, folder):
        self.folder = Path(folder)
        self.folder.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.path = self.folder / 'lifelong.sqlite3'
        self.db = sqlite3.connect(str(self.path), timeout=12., check_same_thread=False, isolation_level=None)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('PRAGMA synchronous=NORMAL')
        self.db.execute('PRAGMA busy_timeout=12000')
        self.db.execute('PRAGMA auto_vacuum=INCREMENTAL')
        self.db.execute('CREATE TABLE IF NOT EXISTS experiences (id INTEGER PRIMARY KEY, scene BLOB NOT NULL, priority REAL NOT NULL, added REAL NOT NULL, data BLOB NOT NULL)')
        self.db.execute('CREATE INDEX IF NOT EXISTS experiences_priority ON experiences(priority)')
        self.db.execute('CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value INTEGER NOT NULL)')
        self.total = int((self.db.execute("SELECT value FROM meta WHERE key='observed'").fetchone() or (0,))[0])
        self.kept = int(self.db.execute('SELECT count(*) FROM experiences').fetchone()[0])
        self.last_saved = 0
        self.last_prune = 0
        self.mean = 0.
        self.variance = 0.
        self.seen = {}
        self.error = ''

    @staticmethod
    def pack(row):
        ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed, efficacy, reserved = row
        header = REPLAY_PACK.pack(action, executed, reward, done, dt, efficacy, reserved, *meta, *nmeta, *ctrl, *intended)
        return zlib.compress(header + ob + nxt, level=1)

    @staticmethod
    def unpack(blob):
        inflater = zlib.decompressobj()
        size = REPLAY_PACK.size + VIS_N * 2
        data = inflater.decompress(blob, size + 1)
        if not inflater.eof or inflater.unused_data or len(data) != size:
            raise ValueError('长期经验记录长度错误')
        values = REPLAY_PACK.unpack(data[:REPLAY_PACK.size])
        action, executed, reward, done, dt, efficacy, reserved = values[:7]
        if action >= ACT_N or executed >= ACT_N or not .001 <= dt <= 2. or not all(math.isfinite(v) for v in values[2:]):
            raise ValueError('长期经验记录无效')
        numeric = values[7:]
        return (data[REPLAY_PACK.size:REPLAY_PACK.size + VIS_N], tuple(numeric[:META_N]), action,
                data[REPLAY_PACK.size + VIS_N:], tuple(numeric[META_N:META_N * 2]),
                float(reward), bool(done), float(dt), tuple(numeric[META_N * 2:META_N * 2 + CTRL_N]),
                tuple(numeric[META_N * 2 + CTRL_N:]), executed, float(efficacy), bool(reserved))

    def remember(self, row):
        if row[12]:
            return
        with self.lock:
            self.total += 1
            magnitude = abs(row[5])
            rate = 1. / math.sqrt(self.total)
            delta = magnitude - self.mean
            self.mean += rate * delta
            self.variance += rate * (delta * delta - self.variance)
            try:
                scene = session_signature(row[0]) + bytes((row[2],))
                visits = self.seen.get(scene, 0) + 1
                self.seen[scene] = visits
                if len(self.seen) > max(REPLAY_LIMIT, int(math.sqrt(max(1, self.total)) * 12)):
                    for key in sorted(self.seen, key=self.seen.get)[:len(self.seen) // 3]:
                        self.seen.pop(key, None)
                surprise = magnitude >= self.mean + math.sqrt(max(0., self.variance))
                periodic = self.total - self.last_saved >= max(1, int(math.sqrt(max(1, self.kept))))
                should_keep = visits == 1 or surprise or periodic or random.random() < 1. / math.sqrt(1. + visits)
                if not should_keep:
                    return
                priority = max(0., magnitude) + 1. / math.sqrt(visits) + max(0., float(row[11])) / math.sqrt(1. + visits)
                self.db.execute('INSERT INTO experiences(scene,priority,added,data) VALUES(?,?,?,?)',
                                (scene, priority, time.time(), self.pack(row)))
                self.kept += 1
                self.last_saved = self.total
                if self.total - self.last_prune >= max(32, int(math.sqrt(max(1, self.kept)))):
                    self.last_prune = self.total
                    self._prune()
                if self.total % max(32, int(math.sqrt(self.total))) == 0:
                    self.db.execute("INSERT INTO meta(key,value) VALUES('observed',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (self.total,))
                self.error = ''
            except (sqlite3.Error, OSError, ValueError, zlib.error) as error:
                self.error = type(error).__name__ + ': ' + str(error)[:140]

    def _prune(self):
        try:
            free = shutil.disk_usage(self.folder).free
            bytes_used = sum(p.stat().st_size for p in (self.path, Path(str(self.path) + '-wal')) if p.exists())
            allowed = max(16 * 1024 * 1024, int((free + bytes_used) / max(4., math.log2(2. + self.kept))))
            if bytes_used <= allowed:
                return
            estimated = max(1, bytes_used // max(1, self.kept))
            excessive = max(1, math.ceil((bytes_used - allowed) / estimated))
            remove = min(max(1, self.kept // 2), max(excessive, int(math.sqrt(self.kept))))
            self.db.execute('DELETE FROM experiences WHERE id IN (SELECT id FROM experiences ORDER BY priority ASC, id ASC LIMIT ?)', (remove,))
            self.kept = int(self.db.execute('SELECT count(*) FROM experiences').fetchone()[0])
            self.db.execute('PRAGMA incremental_vacuum(' + str(min(16384, max(64, int((bytes_used - allowed) / max(1, 4096)))) ) + ')')
            self.db.execute('PRAGMA wal_checkpoint(PASSIVE)')
        except (sqlite3.Error, OSError) as error:
            self.error = str(error)[:140]

    def sample(self, count):
        with self.lock:
            if not self.kept or count <= 0:
                return []
            rows = []
            try:
                first, last = self.db.execute('SELECT min(id),max(id) FROM experiences').fetchone()
                count = min(int(count), self.kept)
                popular = max(1, count // 3)
                ranked = self.db.execute('SELECT data FROM experiences ORDER BY priority DESC LIMIT ?', (min(self.kept, popular * 8),)).fetchall()
                random.shuffle(ranked)
                rows.extend(ranked[:popular])
                remaining = count - len(rows)
                for i in range(remaining):
                    fraction = (i + random.random()) / max(1, remaining)
                    sample_id = random.randint(first, last) if random.random() < .5 else int(first + fraction * (last - first))
                    record = self.db.execute('SELECT data FROM experiences WHERE id >= ? ORDER BY id LIMIT 1', (sample_id,)).fetchone()
                    if record is None:
                        record = self.db.execute('SELECT data FROM experiences ORDER BY id LIMIT 1').fetchone()
                    if record is not None:
                        rows.append(record)
                decoded = []
                for (compressed,) in rows:
                    try:
                        row = self.unpack(compressed)
                        if not row[12]:
                            decoded.append(row)
                    except (ValueError, zlib.error, struct.error):
                        continue
                return decoded
            except (sqlite3.Error, OSError) as error:
                self.error = str(error)[:140]
                return []

    def sync(self):
        with self.lock:
            if self.db is None:
                return
            try:
                self.db.execute("INSERT INTO meta(key,value) VALUES('observed',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (self.total,))
                self.db.execute('PRAGMA wal_checkpoint(PASSIVE)')
            except sqlite3.Error as error:
                self.error = str(error)[:140]

    def close(self):
        with self.lock:
            if self.db is None:
                return
            try:
                self.sync()
            finally:
                self.db.close()
                self.db = None


class GoalAtlas:
    def __init__(self, folder):
        self.path = Path(folder) / 'goals.gz'
        self.lock = threading.RLock()
        self.states = {}
        self.edges = {}
        self.total = 0
        self.current_goal = None
        self.description = '发现可控状态'
        data = read_json(self.path, {})
        if isinstance(data, dict) and data.get('version') == 1:
            try:
                self.states = {str(k): [int(v[0]), float(v[1])] for k, v in data.get('states', {}).items() if len(k) == 16 and len(v) == 2}
                self.edges = {str(k): {str(a): {str(dest): [int(v[0]), float(v[1]), float(v[2])] for dest, v in dests.items() if len(dest) == 16 and len(v) == 3} for a, dests in actions.items()} for k, actions in data.get('edges', {}).items() if len(k) == 16}
                self.total = max(0, int(data.get('total', 0)))
            except (TypeError, ValueError, KeyError, AttributeError):
                self.states, self.edges, self.total = {}, {}, 0

    def signature(self, image):
        cell = coarse_image_cells(image)
        quantized = bytes(max(0, min(15, (cell[index] + cell[index + 1] + cell[index + 2]) // 48)) for index in range(0, PIXELS // 144 * CHANNELS, CHANNELS))
        return hashlib.blake2s(quantized, digest_size=8).hexdigest()

    def observe(self, old, action, new, reward, efficacy, progress):
        source = self.signature(old)
        target = self.signature(new)
        with self.lock:
            self.total += 1
            old_state = self.states.setdefault(source, [0, 0.])
            old_state[0] += 1
            new_state = self.states.setdefault(target, [0, 0.])
            new_state[1] = max(new_state[1] * (1. - 1. / math.sqrt(1. + old_state[0])), max(0., reward) * efficacy * float(progress))
            destinations = self.edges.setdefault(source, {}).setdefault(str(action), {})
            entry = destinations.setdefault(target, [0, 0., 0.])
            entry[0] += 1
            entry[1] += float(reward)
            entry[2] += float(efficacy)
            limit = max(REPLAY_LIMIT * 2, int(math.sqrt(self.total) * 16))
            if len(self.states) > limit:
                old_keys = sorted(self.states, key=lambda key: (self.states[key][0], self.states[key][1]))[:max(1, len(self.states) // 8)]
                for key in old_keys:
                    self.states.pop(key, None)
                    self.edges.pop(key, None)
                known = self.states.keys()
                for actions in self.edges.values():
                    for targets in actions.values():
                        for key in tuple(targets):
                            if key not in known:
                                del targets[key]

    def plan(self, image, allowed):
        origin = self.signature(image)
        with self.lock:
            if origin not in self.edges or not self.edges[origin]:
                self.description = f'发现新状态 · 已建立 {len(self.states)} 个状态'
                return None
            frontier = [(0., 0, origin, None, 1.)]
            seen = set()
            horizon = max(1, int(math.log2(2. + len(self.states))))
            best = None
            budget = max(8, int(math.sqrt(len(self.states)) * 4))
            while frontier and len(seen) < budget:
                distance, depth, current, first_action, confidence = heapq.heappop(frontier)
                if current in seen or depth > horizon:
                    continue
                seen.add(current)
                for action_str, destinations in self.edges.get(current, {}).items():
                    action = int(action_str)
                    if depth == 0 and action not in allowed:
                        continue
                    trials = sum(entry[0] for entry in destinations.values())
                    for next_state, (count, total_reward, total_effectiveness) in destinations.items():
                        if next_state not in self.states or count <= 0:
                            continue
                        likelihood = count / max(1, trials)
                        quality = total_effectiveness / count
                        next_probability = confidence * likelihood * quality
                        visit = self.states[next_state][0]
                        gain = max(0., total_reward / count) + self.states[next_state][1] + 1. / math.sqrt(1. + visit)
                        gain *= next_probability / (1. + depth + (next_state == origin))
                        gain *= count / (count + math.sqrt(max(1, trials)))
                        if next_state != current and (best is None or gain > best[0]):
                            best = (gain, action if first_action is None else first_action, next_state, next_probability, depth + 1)
                        if next_state not in seen and depth < horizon and next_probability > 0.:
                            heapq.heappush(frontier, (distance + 1. / max(.01, next_probability), depth + 1, next_state, action if first_action is None else first_action, next_probability))
            if best is None:
                self.description = f'复核已知状态 · {len(self.states)} 个状态'
                return None
            score, action, goal, confidence, length = best
            self.current_goal = goal
            self.description = f'自主规划 {length} 步目标 · 状态 {len(self.states)} · 路径可靠度 {confidence:.0%}'
            trust = confidence * (1. - adaptive_exploration(self.total, self.states[origin][0]))
            return (action, min(1., max(0., trust)), score)

    def save(self):
        with self.lock:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            save_json(self.path, {'version': 1, 'total': self.total, 'states': self.states, 'edges': self.edges})


class LiteBrain:
    def __init__(self, folder):
        self.folder = folder
        self.archive = LifelongMemory(folder)
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
        self.sleep_audit = None
        self.save_lock = threading.RLock()
        self.checkpoint_lock = threading.Lock()
        latest = newest_replay(folder)
        recovered = [latest] if latest is not None else []
        for generation, slot, records in recovered:
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
            generation, slot, records = recovered[0]
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
        if self.memory and not self.archive.kept:
            for row in self.memory:
                self.archive.remember(row)

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
        cells = coarse_image_cells(ob)
        out = []
        for index in range(0, len(cells), CHANNELS):
            colors = cells[index:index + CHANNELS]
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

    def values(self, ob, meta, keys=None):
        values = [self.table[key] for key in (keys if keys is not None else self.keys(ob, meta)) if key in self.table]
        if not values:
            return None
        return [sum(part[action] for part in values) / len(values) for action in range(ACT_N)]

    def choose(self, ob, meta, held, targets=None):
        opts = candidates(held)
        with self.save_lock:
            keys = self.keys(ob, meta)
            q = self.values(ob, meta, keys)
            visits = sum(self.visits.get(key, 0) for key in keys)
            epsilon = adaptive_exploration(self.steps, visits, 1. / math.sqrt(1. + len(keys) if q is not None else 1.))
            exploring = q is None or random.random() < epsilon
            if exploring:
                choice = explore_action(opts, meta, self.steps, ob, targets)
                return choice, exploratory_control(choice, meta)
            choice = careful_choice(q, opts, visits)
            controls = [(self.actor[k + bytes([choice])], self.visits.get(k, 0)) for k in keys if k + bytes([choice]) in self.actor]
            if controls:
                weight = sum(w for _, w in controls)
                predicted = [sum(vec[i] * w for vec, w in controls) / max(1, weight) for i in range(CTRL_N)]
                confidence = visits / (1. + visits)
                return choice, anchor_control(choice, predicted, confidence)
            return choice, anchor_control(choice)

    def update(self, row):
        ob, meta, action, nxt, nmeta, reward, done, dt = row[:8]
        keys = self.keys(ob, meta)
        before = self.values(ob, meta, keys)
        after = self.values(nxt, nmeta)
        held = {'l': nmeta[9] > .5, 'r': nmeta[10] > .5, 'm': nmeta[11] > .5}
        future = max(after[i] for i in candidates(held)) if after else 0.
        target = reward + (0 if done else (.975 ** (dt / .075)) * future)
        baseline = before[action] if before is not None else 0.
        correction = (target - baseline) / math.sqrt(1. + self.visits.get(keys[0], 0))
        for key in keys:
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
        if len(self.table) > REPLAY_LIMIT * len(keys):
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
        self.archive.remember(row)

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.memory)
            selected_ids = set(map(id, self.train_memory)) if self.train_memory is not None else None
            indices = [i for i, row in enumerate(source) if not row[12] and (selected_ids is None or id(row) in selected_ids)]
        if not indices:
            return 0
        total = 0
        archive_rows = self.archive.sample(min(max(2, int(math.sqrt(count))), max(2, len(indices))))
        sampler = ReplaySampler(source, indices)
        with self.save_lock:
            for step in range(count):
                if stop.is_set():
                    break
                if archive_rows and step % max(2, int(math.sqrt(len(indices)))) == 0:
                    self.update(random.choice(archive_rows))
                else:
                    self.update(multi_step_experience(source, sampler.draw(1)[0]))
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
            self.sleep_audit = None
            split = sleep_split(list(self.memory))
            if split is None:
                self.train_memory = []
                return
            self.train_memory, validation, audit = split
            audit_labels = self.validation_targets(audit)
            self.sleep_audit = (audit, audit_labels, self.evaluate(audit, audit_labels), self.policy_metric(audit))
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
            audit = self.sleep_audit
            self.sleep_audit = None
            current = self.policy_metric(records)
            if best is not None:
                self.table, self.actor, self.visits = best[2:5]
                if audit is not None:
                    audit_rows, audit_targets, audit_before, audit_policy = audit
                    audit_after = self.evaluate(audit_rows, audit_targets)
                    audit_current = self.policy_metric(audit_rows)
                    tolerance = max(1e-6, abs(audit_before) * .002)
                    if not math.isfinite(audit_after) or audit_after > audit_before + tolerance or (audit_policy is not None and audit_current is not None and audit_current + .015 < audit_policy):
                        self.table, self.actor, self.visits = snapshot, previous_actor, previous_visits
                        return False, before, audit_after, quality, audit_current
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
            self.archive.sync()
            with self.save_lock:
                self.generation, self.latest_replay_generation, self.slot = generation, generation, slot
            discard_recovery(self.folder, generation)

    def close(self):
        self.archive.close()

class TorchBrain:
    def __init__(self, folder, torch, device, label):
        self.folder = folder
        self.archive = LifelongMemory(folder)
        self.historical_samples = []
        self.historical_refreshed = -1
        self.sampler = None
        self.sampler_key = None
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

        class GrowingLayer(nn.Module):
            def __init__(self, dimensions):
                super().__init__()
                self.transform = nn.Sequential(nn.LayerNorm(dimensions), nn.Linear(dimensions, dimensions * 2), nn.GELU(), nn.Linear(dimensions * 2, dimensions))
                nn.init.zeros_(self.transform[-1].weight)
                nn.init.zeros_(self.transform[-1].bias)

            def forward(self, features):
                return features + self.transform(features)

        class GrowingSpatialLayer(nn.Module):
            def __init__(self, channels):
                super().__init__()
                hidden = channels * 2
                self.transform = nn.Sequential(nn.GroupNorm(max(1, math.gcd(channels, 8)), channels), nn.Conv2d(channels, hidden, 3, padding=1), nn.GELU(), nn.Conv2d(hidden, channels, 3, padding=1))
                nn.init.zeros_(self.transform[-1].weight)
                nn.init.zeros_(self.transform[-1].bias)

            def forward(self, features):
                return features + self.transform(features)

        class Net(nn.Module):
            def __init__(self):
                super().__init__()
                self.vision = nn.Sequential(nn.Conv2d(CHANNELS * 2, 24, 5, stride=2, padding=2), nn.GELU(), nn.Conv2d(24, 48, 3, stride=2, padding=1), nn.GELU(), nn.Conv2d(48, 64, 3, stride=2, padding=1), nn.GELU(), nn.AdaptiveAvgPool2d((4, 6)))
                self.visual_projection = nn.Sequential(nn.Flatten(), nn.Linear(64 * 4 * 6, 160), nn.GELU())
                self.visual_attention = nn.Conv2d(64, 1, 1)
                self.visual_context = nn.Linear(64, 160)
                self.visual_norm = nn.LayerNorm(160)
                self.visual_growing = nn.ModuleList()
                self.reconstruction = nn.Sequential(nn.Linear(160 + META_N, 256), nn.GELU(), nn.Linear(256, CHANNELS * 2 * 8 * 12), nn.Sigmoid())
                self.policy = nn.Sequential(nn.Linear(160 + META_N, 192), nn.GELU(), nn.Linear(192, ACT_N))
                self.control = nn.Sequential(nn.Linear(160 + META_N, 128), nn.GELU(), nn.Linear(128, ACT_N * CTRL_N), nn.Tanh())
                self.effect = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 160), nn.GELU(), nn.Linear(160, 1))
                self.execution = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 128), nn.GELU(), nn.Linear(128, 1), nn.Sigmoid())
                self.dynamics = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 192), nn.GELU(), nn.Linear(192, 160 + META_N))
                self.dynamics_alternative = nn.Sequential(nn.Linear(160 + META_N + CTRL_N, 192), nn.GELU(), nn.Linear(192, 160 + META_N))
                self.world_models = nn.ModuleList()
                self.inverse = nn.Sequential(nn.Linear((160 + META_N) * 2, 192), nn.GELU(), nn.Linear(192, ACT_N))
                self.growing = nn.ModuleList()

            def grow(self):
                device = next(self.parameters()).device
                layer = GrowingLayer(160 + META_N).to(device)
                self.growing.append(layer)
                return list(layer.parameters())

            def grow_visual(self):
                device = next(self.parameters()).device
                layer = GrowingSpatialLayer(64).to(device)
                self.visual_growing.append(layer)
                return list(layer.parameters())

            def grow_world_model(self):
                device = next(self.parameters()).device
                head = copy.deepcopy(self.dynamics_alternative).to(device)
                self.world_models.append(head)
                return list(head.parameters())

            def policy_controls(self, embedding):
                raw = self.control(embedding).reshape(-1, ACT_N, CTRL_N)
                return torch.cat((raw[..., :2], (raw[..., 2:3] + 1.) * .5, raw[..., 3:7], (raw[..., 7:8] + 1.) * .5), dim=-1)

            def forward(self, frames, meta):
                spatial = self.vision(frames)
                for layer in self.visual_growing:
                    spatial = layer(spatial)
                attention = torch.softmax(self.visual_attention(spatial).flatten(2), dim=-1)
                context = (spatial.flatten(2) * attention).sum(dim=-1)
                visual = self.visual_norm(self.visual_projection(spatial) + self.visual_context(context))
                embedding = torch.cat((visual, meta), dim=1)
                for layer in self.growing:
                    embedding = layer(embedding)
                return self.policy(embedding), self.policy_controls(embedding), embedding

            def reconstruct(self, embedding):
                return self.reconstruction(embedding)

            def effect_value(self, embedding, controls):
                return self.effect(torch.cat((embedding, controls), dim=-1)).squeeze(-1)

            def execute_value(self, embedding, controls):
                return self.execution(torch.cat((embedding, controls), dim=-1)).squeeze(-1)

            def next_features(self, embedding, controls):
                return self.dynamics(torch.cat((embedding, controls), dim=-1))

            def next_features_alternative(self, embedding, controls):
                return self.dynamics_alternative(torch.cat((embedding, controls), dim=-1))

            def world_predictions(self, embedding, controls):
                inputs = torch.cat((embedding, controls), dim=-1)
                return torch.stack([self.dynamics(inputs), self.dynamics_alternative(inputs), *(head(inputs) for head in self.world_models)], dim=0)

            def predict_with_uncertainty(self, embedding, controls):
                predictions = self.world_predictions(embedding, controls)
                mean = predictions.mean(dim=0)
                disagreement = predictions.var(dim=0, unbiased=False).mean(dim=-1) * 4.
                return mean, disagreement

            def infer_action(self, before, after):
                return self.inverse(torch.cat((before, after), dim=-1))

        if getattr(device, 'type', None) == 'cuda':
            torch.backends.cudnn.benchmark = True
            if hasattr(torch.backends.cuda.matmul, 'allow_tf32'):
                torch.backends.cuda.matmul.allow_tf32 = True
        self.use_bfloat16 = False
        self.use_float16 = False
        self.grad_scaler = None
        self.perf = {'transfer_ms': 0., 'inference_ms': 0., 'batches': 0, 'training_examples': 0, 'visual_error': 0.}
        if getattr(device, 'type', None) == 'cuda':
            try:
                self.use_bfloat16 = bool(torch.cuda.is_bf16_supported())
                self.use_float16 = not self.use_bfloat16 and torch.cuda.get_device_capability(device)[0] >= 7
                if self.use_float16:
                    self.grad_scaler = torch.amp.GradScaler('cuda')
            except (AttributeError, RuntimeError, TypeError):
                self.use_float16 = False
                self.grad_scaler = None
        self.q = Net().to(device)
        if getattr(device, 'type', None) == 'cuda':
            self.q = self.q.to(memory_format=torch.channels_last)
        self.target = copy.deepcopy(self.q).to(device)
        self.target.eval()
        self.optq = torch.optim.AdamW(self.q.parameters(), lr=1. / math.sqrt(VIS_N * (160 + META_N)), weight_decay=1. / VIS_N)
        self.growth_at_step = 0
        self.growth_attempts = 0
        self.world_growth_at_step = 0
        self.visual_growth_at_step = 0
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
        self.interactive_budget = None
        self.gpu_train_started = 0.
        self.gpu_train_examples = 0
        self.gpu_train_batches = 0
        self.steps = 0
        self.grads = 0
        self.train_memory = None
        self.sleep_evaluation = None
        self.sleep_best = None
        self.sleep_audit = None
        self.planning_trust = 0.
        self.planning_ratio = None
        self.sleep_initial_capacity = None
        replay_pairs = list(replay_sources(folder))
        if replay_pairs:
            self.generation, recovered_slot, self.memory = max(replay_pairs, key=lambda entry: (entry[0], entry[1] != 'recovery'))
            self.slot = recovered_slot if isinstance(recovered_slot, int) else -1
        replay_generations = {slot: generation for generation, slot, _ in replay_pairs if isinstance(slot, int)}
        replay_counts = {slot: len(records) for generation, slot, records in replay_pairs if isinstance(slot, int)}
        for slot in sorted(replay_generations, key=lambda index: replay_generations[index]):
            path = folder / f'model.{slot}.pt'
            if not path.exists():
                continue
            try:
                state = torch.load(path, map_location='cpu', weights_only=True)
                if state.get('version') not in (15, 16, 17):
                    continue
                depth = int(state.get('capacity_depth', 0))
                worlds = int(state.get('capacity_world_models', 0))
                visual_depth = int(state.get('capacity_visual_depth', 0))
                if depth < 0 or worlds < 0 or visual_depth < 0 or depth != sum(key.startswith('growing.') and key.endswith('.transform.3.weight') for key in state.get('q', {})) or worlds != sum(key.startswith('world_models.') and key.endswith('.2.weight') for key in state.get('q', {})) or visual_depth != sum(key.startswith('visual_growing.') and key.endswith('.transform.3.weight') for key in state.get('q', {})):
                    continue
                generation = int(state['generation'])
                if generation <= self.model_generation or generation != replay_generations[slot] or state.get('replay_count', replay_counts[slot]) != replay_counts[slot]:
                    continue
                old_depth = len(self.q.growing)
                old_worlds = len(self.q.world_models)
                old_visual_depth = len(self.q.visual_growing)
                before_q = copy.deepcopy(self.q.state_dict())
                before_target = copy.deepcopy(self.target.state_dict())
                before_opt = copy.deepcopy(self.optq.state_dict())
                try:
                    self.resize_capacity(depth, worlds, visual_depth)
                    self.q.load_state_dict(state['q'], strict=True)
                    self.target.load_state_dict(state['target'], strict=True)
                    self.optq.load_state_dict(state['opt'])
                    for group in self.optq.state.values():
                        for key, value in group.items():
                            if torch.is_tensor(value):
                                group[key] = value.to(device)
                except Exception:
                    self.resize_capacity(old_depth, old_worlds, old_visual_depth)
                    self.q.load_state_dict(before_q)
                    self.target.load_state_dict(before_target)
                    self.optq.load_state_dict(before_opt)
                    raise
                self.growth_at_step = max(0, int(state.get('growth_at_step', 0)))
                self.growth_attempts = max(0, int(state.get('growth_attempts', depth)))
                self.world_growth_at_step = max(0, int(state.get('world_growth_at_step', 0)))
                self.visual_growth_at_step = max(0, int(state.get('visual_growth_at_step', 0)))
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
        if self.memory and not self.archive.kept:
            for row in self.memory:
                self.archive.remember(row)
        if self.model_generation and self.memory:
            split = sleep_split(list(self.memory))
            if split is not None:
                try:
                    self.calibrate_planning(split[2])
                except (RuntimeError, ValueError):
                    self.planning_trust = 0.

    def resize_capacity(self, depth, world_count=None, visual_depth=None):
        with self.model_lock:
            world_count = len(self.q.world_models) if world_count is None else max(0, int(world_count))
            visual_depth = len(self.q.visual_growing) if visual_depth is None else max(0, int(visual_depth))
            depth = max(0, int(depth))
            def forget(parameters):
                selected = set(parameters)
                for index in range(len(self.optq.param_groups) - 1, 0, -1):
                    group = self.optq.param_groups[index]
                    if selected.intersection(group['params']):
                        self.optq.param_groups.pop(index)
                        for parameter in group['params']:
                            self.optq.state.pop(parameter, None)
                        return
                raise RuntimeError('计算容量与优化器状态不匹配')
            while len(self.q.visual_growing) > visual_depth:
                forget(list(self.q.visual_growing[-1].parameters()))
                self.q.visual_growing.pop(-1)
                self.target.visual_growing.pop(-1)
            while len(self.q.world_models) > world_count:
                forget(list(self.q.world_models[-1].parameters()))
                self.q.world_models.pop(-1)
                self.target.world_models.pop(-1)
            while len(self.q.growing) > depth:
                forget(list(self.q.growing[-1].parameters()))
                self.q.growing.pop(-1)
                self.target.growing.pop(-1)
            while len(self.q.growing) < depth:
                insertion = 1 + len(self.q.growing)
                parameters = self.q.grow()
                self.target.grow()
                self.optq.add_param_group({'params': parameters})
                self.optq.param_groups.insert(insertion, self.optq.param_groups.pop())
            while len(self.q.world_models) < world_count:
                insertion = 1 + len(self.q.growing) + len(self.q.world_models)
                parameters = self.q.grow_world_model()
                self.target.grow_world_model()
                self.optq.add_param_group({'params': parameters})
                self.optq.param_groups.insert(insertion, self.optq.param_groups.pop())
            while len(self.q.visual_growing) < visual_depth:
                parameters = self.q.grow_visual()
                self.target.grow_visual()
                self.optq.add_param_group({'params': parameters})
            self.target.eval()

    def grow_from_evidence(self, records):
        if not records:
            return False
        diverse = len({session_signature(row[0]) for row in records})
        parameters = sum(parameter.numel() for parameter in self.q.parameters())
        depth = len(self.q.growing)
        worlds = len(self.q.world_models)
        visual_depth = len(self.q.visual_growing)
        layer_evidence = max(8, int(math.log2(2. + parameters) * math.sqrt(1. + depth)))
        model_evidence = max(layer_evidence, int(math.sqrt(2. + parameters) * math.sqrt(1. + worlds)))
        visual_evidence = max(layer_evidence, int(math.log2(2. + parameters) * math.sqrt(2. + visual_depth) * 2))
        grow_layer = diverse >= layer_evidence and self.steps - self.growth_at_step >= layer_evidence
        grow_model = diverse >= model_evidence and self.steps - self.world_growth_at_step >= model_evidence
        grow_visual = diverse >= visual_evidence and self.steps - self.visual_growth_at_step >= visual_evidence
        if not grow_layer and not grow_model and not grow_visual:
            return False
        layer_parameters = (160 + META_N) * ((160 + META_N) * 2 + 1) + (160 + META_N) * 2 * ((160 + META_N) + 1) + 2 * (160 + META_N)
        world_parameters = sum(parameter.numel() for parameter in self.q.dynamics_alternative.parameters())
        visual_parameters = 64 * 2 + (64 * 128 + 128 * 64) * 9 + 128 + 64
        needed = (layer_parameters * int(grow_layer) + world_parameters * int(grow_model) + visual_parameters * int(grow_visual)) * 48
        free = available_memory()
        if getattr(self.d, 'type', None) == 'cuda':
            try:
                free = self.t.cuda.mem_get_info(self.d)[0]
            except (RuntimeError, AttributeError):
                return False
        if free and free < needed:
            return False
        self.resize_capacity(depth + int(grow_layer), worlds + int(grow_model), visual_depth + int(grow_visual))
        if grow_layer:
            self.growth_at_step = self.steps
        if grow_model:
            self.world_growth_at_step = self.steps
        if grow_visual:
            self.visual_growth_at_step = self.steps
        self.growth_attempts += 1
        return True

    def reconstruct_from_memory(self):
        with self.save_lock:
            records = [row for row in self.memory if not row[12]]
        if len(records) < 2:
            return 0
        budget = max(1, int(math.sqrt(len(records)) * math.log2(2 + len(records))))
        return self.train(budget, AnyStop())

    def restore_experience(self, records, steps, rebuild=True):
        with self.save_lock:
            self.memory = deque(records, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.sampler_key = None
        return self.reconstruct_from_memory() if rebuild else 0

    def distill_policy(self, samples, stop):
        if not samples or stop.is_set():
            return 0
        t = self.t
        trained = 0
        with self.model_lock:
            self.q.train()
            try:
                chunk_size = max(1, min(len(samples), self.batch_sizes[False]))
                for start in range(0, len(samples), chunk_size):
                    if stop.is_set():
                        break
                    rows = samples[start:start + chunk_size]
                    frames = self.images([row[0] for row in rows])
                    features = t.tensor([row[1] for row in rows], dtype=t.float32, device=self.d)
                    teacher = t.tensor([row[2] for row in rows], dtype=t.float32, device=self.d)
                    teacher = teacher - teacher.mean(dim=-1, keepdim=True)
                    spread = teacher.square().mean(dim=-1, keepdim=True).sqrt().clamp(min=1e-5)
                    weights = t.softmax(teacher / spread, dim=-1)
                    with self.autocast():
                        predicted = self.q(frames, features)[0]
                        loss = -(weights * t.log_softmax(predicted, dim=-1)).sum(dim=-1).mean()
                    if not bool(t.isfinite(loss).item()):
                        raise ValueError('策略迁移出现非有限训练误差')
                    self.optq.zero_grad(set_to_none=True)
                    if self.grad_scaler is not None:
                        self.grad_scaler.scale(loss).backward()
                        self.grad_scaler.unscale_(self.optq)
                        t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.)
                        self.grad_scaler.step(self.optq)
                        self.grad_scaler.update()
                    else:
                        loss.backward()
                        t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.)
                        self.optq.step()
                    self.grads += 1
                    trained += len(rows)
                if trained:
                    self.target.load_state_dict(self.q.state_dict())
                    self.target.eval()
            finally:
                self.q.eval()
        return trained

    def append_experience(self, records, steps):
        with self.save_lock:
            self.memory.extend(records)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.sampler_key = None
        return len(records)

    def autocast(self):
        if getattr(self.d, 'type', None) == 'cuda':
            if self.use_bfloat16:
                return self.t.autocast(device_type='cuda', dtype=self.t.bfloat16)
            if self.use_float16:
                return self.t.autocast(device_type='cuda', dtype=self.t.float16)
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

    def choose(self, ob, meta, held, targets=None):
        allowed = candidates(held)
        epsilon = adaptive_exploration(self.steps, self.grads)
        if random.random() < epsilon:
            action = explore_action(allowed, meta, self.steps, ob, targets)
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
                    confidence *= self.grads / (self.grads + math.sqrt(max(1, len(self.memory))))
                    metric = q[0] + confidence * (returns * likelihood - returns.detach().mean())
                    imagined, disagreement = self.q.predict_with_uncertainty(expanded, candidate)
                    if self.grads > 0:
                        spread = q[0].detach().std(unbiased=False)
                        uncertainty = disagreement.clamp_min(1e-12).sqrt()
                        novelty = (uncertainty - uncertainty.mean()) / uncertainty.std(unbiased=False).clamp_min(1e-6)
                        metric = metric + epsilon * spread * novelty * likelihood
                    if self.planning_trust > 0. and self.grads > 0:
                        discount = self.planning_trust * confidence
                        planning_reliability = (1. + disagreement.sqrt()).reciprocal()
                        evidence = math.log2(2. + max(0, self.grads))
                        depth = max(1, int(1. + evidence * self.planning_trust / math.sqrt(1. + max(0., self.planning_ratio or 0.))))
                        scale = q[0].detach().std(unbiased=False).clamp(min=1e-6)
                        for _ in range(depth):
                            future_values = self.q.policy(imagined)[:, :17]
                            future_action = future_values.argmax(dim=1)
                            utility = future_values.gather(1, future_action[:, None]).squeeze(1)
                            advantage = (utility - utility.mean()).clamp(-scale, scale)
                            metric = metric + discount * planning_reliability * likelihood * advantage
                            discount *= self.planning_trust * .975
                            if discount < 1. / max(1., self.steps + self.grads):
                                break
                            control_options = self.q.policy_controls(imagined)[:, :17]
                            imagined_control = control_options.gather(1, future_action[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
                            likelihood = likelihood * self.q.execute_value(imagined, imagined_control)
                            imagined, disagreement = self.q.predict_with_uncertainty(imagined, imagined_control)
                            planning_reliability = planning_reliability / (1. + disagreement.sqrt())
                payload = self.t.cat((metric.float(), output[0].float().reshape(-1), likelihood.float())).cpu().tolist()
                values = payload[:ACT_N]
                action = careful_choice(values, allowed, self.grads)
                offset = ACT_N + action * CTRL_N
                control = payload[offset:offset + CTRL_N]
                predicted_efficacy = payload[ACT_N * (CTRL_N + 1) + action]
                trust = confidence * predicted_efficacy / max(1e-7, predicted_efficacy + (1. - predicted_efficacy) * epsilon)
        elapsed = (time.monotonic() - inference_started) * 1000.
        self.perf['inference_ms'] += (elapsed - self.perf['inference_ms']) / math.sqrt(1. + self.steps)
        return action, anchor_control(action, control, trust)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False):
        row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved))
        with self.save_lock:
            self.memory.append(row)
            self.steps += 1
        self.archive.remember(row)

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.memory)
            selected_ids = set(map(id, self.train_memory)) if self.train_memory is not None else None
            indices = [i for i, row in enumerate(source) if not row[12] and (selected_ids is None or id(row) in selected_ids)]
        if len(indices) < 2:
            return 0
        if self.train_memory is None and len(indices) > max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1)))):
            width = max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1))))
            old = indices[:-width]
            indices = random.sample(old, min(len(old), max(1, width // 2))) + indices[-width:]
        sampler_key = (self.steps, len(source), len(indices), self.train_memory is not None)
        if self.sampler_key != sampler_key:
            self.sampler = ReplaySampler(source, indices)
            self.sampler_key = sampler_key
        if self.historical_refreshed < 0 or self.grads - self.historical_refreshed >= max(1, int(math.sqrt(1. + self.grads))):
            self.historical_samples = self.archive.sample(min(max(8, int(math.sqrt(len(indices)) * 2)), self.batch_sizes[self.train_memory is not None]))
            self.historical_refreshed = self.grads
        with self.model_lock:
            self.gpu_train_batches = 0
            self.gpu_train_examples = 0
            self.q.train()
            try:
                while not stop.is_set():
                    try:
                        return self._train_locked(count, stop, source, indices)
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

    def _train_locked(self, count, stop, source, indices):
        t = self.t
        count_done = 0
        sleeping = self.train_memory is not None
        for _ in range(count):
            if stop.is_set():
                break
            started = time.monotonic()
            requested_batch = min(self.batch_sizes[sleeping], len(indices))
            if not sleeping and self.interactive_budget:
                throughput = self.training_throughput[False]
                if throughput > 0.:
                    requested_batch = min(requested_batch, max(1, int(throughput * self.interactive_budget)))
                else:
                    requested_batch = min(requested_batch, max(1, int(math.sqrt(requested_batch))))
            sampled = self.sampler.draw(requested_batch)
            immediate = [source[i] for i in sampled]
            batch = [multi_step_experience(source, i) for i in sampled]
            if self.historical_samples and len(batch) > 1:
                older = random.choices(self.historical_samples, k=max(1, len(batch) // 4))
                batch[:len(older)] = older
                immediate[:len(older)] = older
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
            immediate_reward = t.tensor([row[5] for row in immediate], dtype=t.float32, device=self.d)
            immediate_future = self.images([row[3] for row in immediate])
            immediate_meta = t.tensor([row[4] for row in immediate], dtype=t.float32, device=self.d)
            with self.autocast():
                qvalues, predicted_all, embedding = self.q(state, meta)
            qvalues, predicted_all, embedding = qvalues.float(), predicted_all.float(), embedding.float()
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
                next_q, _, _ = self.target(future, nmeta)
                after = next_q.gather(1, best).squeeze(1)
                future_features = self.target(immediate_future, immediate_meta)[2]
                discount = (.975 ** (dt / .075)) * (1 - done)
                targets = rew + discount * after
                effect_targets = immediate_reward
            visual_target = t.nn.functional.adaptive_avg_pool2d(state, (8, 12)).flatten(1)
            visual_loss = t.nn.functional.smooth_l1_loss(self.q.reconstruct(embedding), visual_target)
            temporal = t.nn.functional.smooth_l1_loss(values, targets)
            effect_loss = t.nn.functional.smooth_l1_loss(effectiveness, effect_targets)
            execution_loss = t.nn.functional.smooth_l1_loss(execution, efficacy)
            futures = self.q.world_predictions(embedding, ctrl)
            predicted_future = futures.mean(dim=0)
            per_head = t.nn.functional.smooth_l1_loss(futures, future_features.detach().unsqueeze(0).expand_as(futures), reduction='none').mean(dim=-1)
            if len(batch) > 1:
                bootstrap = (t.rand_like(per_head) < 1. - math.exp(-1.)).to(per_head.dtype)
                bootstrap = bootstrap + (bootstrap.sum(dim=1, keepdim=True) == 0).to(bootstrap.dtype)
                dynamics_loss = (per_head * bootstrap).sum() / bootstrap.sum().clamp(min=1.)
            else:
                dynamics_loss = per_head.mean()
            evidence = (state - immediate_future).abs().mean(dim=(1, 2, 3)).detach() * efficacy
            inverse_errors = t.nn.functional.cross_entropy(self.q.infer_action(embedding, future_features.detach()), acts, reduction='none')
            inverse_loss = (inverse_errors * evidence).sum() / evidence.sum().clamp(min=1e-6)
            if len(batch) > 1:
                projection = t.nn.functional.normalize(predicted_future, dim=-1)
                teachers = t.nn.functional.normalize(future_features.detach(), dim=-1)
                logits = (projection @ teachers.T) * math.sqrt(projection.shape[-1])
                signatures = [session_signature(row[3]) for row in immediate]
                duplicate = t.tensor([[i != j and signatures[i] == signatures[j] for j in range(len(signatures))] for i in range(len(signatures))], dtype=t.bool, device=self.d)
                contrastive_loss = t.nn.functional.cross_entropy(logits.masked_fill(duplicate, -1e4), t.arange(len(batch), device=self.d))
            else:
                contrastive_loss = dynamics_loss * 0.
            advantage = (immediate_reward - effectiveness.detach()).clamp(-1., 1.)
            good = t.sigmoid(advantage / immediate_reward.detach().std(unbiased=False).clamp(min=1e-4))
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
            confidence = (1. - adaptive_exploration(self.steps, self.grads)) * immediate_reward.detach().std(unbiased=False).clamp(min=1e-5) / (immediate_reward.detach().std(unbiased=False).clamp(min=1e-5) + effect_loss.detach())
            dynamics_weight = (temporal.detach() + effect_loss.detach() + 1e-6) / (temporal.detach() + effect_loss.detach() + dynamics_loss.detach() + 1e-6)
            visual_weight = (temporal.detach() + effect_loss.detach() + dynamics_loss.detach() + 1e-6) / (temporal.detach() + effect_loss.detach() + dynamics_loss.detach() + visual_loss.detach() + 1e-6)
            loss = temporal + effect_loss + execution_loss + auxiliary + visual_weight * visual_loss + dynamics_weight * (dynamics_loss + inverse_loss + contrastive_loss) - confidence * actor_gain
            if not bool(t.isfinite(loss).item()):
                raise ValueError('模型训练数值异常')
            self.optq.zero_grad(set_to_none=True)
            if self.grad_scaler is not None:
                self.grad_scaler.scale(loss).backward()
                self.grad_scaler.unscale_(self.optq)
                t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.0)
                self.grad_scaler.step(self.optq)
                self.grad_scaler.update()
            else:
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
                visual_metric = float(visual_loss.detach().item())
                self.perf['visual_error'] += (visual_metric - self.perf['visual_error']) / math.sqrt(1. + self.grads)
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
                self.batch_sizes[sleeping] = max(1, min(len(indices), self.batch_limits[sleeping], proposed))
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
                visual_target = t.nn.functional.adaptive_avg_pool2d(frames, (8, 12)).flatten(1)
                visual_loss = t.nn.functional.smooth_l1_loss(self.q.reconstruct(features), visual_target, reduction='none').mean(dim=1).sum()
                selected_controls = all_controls.gather(1, actions[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
                teacher = (controls * efficacy[:, None] + intended * (1. - efficacy[:, None]))
                actor_loss = ((selected_controls - teacher).square().mean(dim=1) * efficacy).sum()
                effect_loss = t.nn.functional.smooth_l1_loss(self.q.effect_value(features, controls), rewards, reduction='sum')
                execution_loss = t.nn.functional.smooth_l1_loss(self.q.execute_value(features, intended), efficacy, reduction='sum')
                next_frames = self.images([row[3] for row in segment])
                next_meta = t.tensor([row[4] for row in segment], dtype=t.float32, device=self.d)
                next_features = self.target(next_frames, next_meta)[2]
                evidence = (frames - next_frames).abs().mean(dim=(1, 2, 3)) * efficacy
                inverse_loss = (t.nn.functional.cross_entropy(self.q.infer_action(features, next_features), actions, reduction='none') * evidence).sum() / evidence.sum().clamp(min=1e-6)
                estimated, disagreement = self.q.predict_with_uncertainty(features, controls)
                dynamics_loss = (t.nn.functional.smooth_l1_loss(estimated, next_features, reduction='none').mean(dim=1) + disagreement.sqrt()).sum()
                total += float((q_loss + effect_loss + execution_loss + dynamics_loss + actor_loss + visual_loss + inverse_loss * len(segment)).cpu())
        return total / max(1, len(entries))

    def performance(self):
        with self.save_lock:
            training = self.training_throughput[self.train_memory is not None]
            metrics = {'world_models': 2 + len(self.q.world_models), 'transfer_ms': round(self.perf['transfer_ms'], 3), 'inference_ms': round(self.perf['inference_ms'], 3), 'training_samples_per_second': round(training, 2), 'batches': self.perf['batches'], 'training_examples': self.perf['training_examples'], 'visual_error': round(self.perf['visual_error'], 5), 'batch_size': self.batch_sizes[self.train_memory is not None], 'archive_count': self.archive.kept, 'archive_total_observed': self.archive.total, 'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'model_parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'planning_trust': round(self.planning_trust, 3), 'world_model_ratio': round(self.planning_ratio, 3) if self.planning_ratio is not None else None}
            if getattr(self.d, 'type', None) == 'cuda':
                try:
                    free, total = self.t.cuda.mem_get_info(self.d)
                    metrics['gpu_memory_used_gb'] = round((total - free) / 1073741824., 2)
                    metrics['gpu_memory_total_gb'] = round(total / 1073741824., 2)
                except RuntimeError:
                    pass
            return metrics

    def dynamics_metric(self, records):
        valid = [row for row in records if not row[6] and row[11] > 0.]
        if not valid:
            return None
        threshold = sorted(row[11] for row in valid)[len(valid) // 2]
        records = [row for row in valid if row[11] >= threshold]
        if len(records) < max(4, int(math.log2(2. + len(self.memory)))):
            return None
        t = self.t
        mistake = 0.
        baseline = 0.
        disagreements = 0.
        examples = 0
        self.q.eval()
        with t.no_grad():
            for offset in range(0, len(records), max(1, self.batch_sizes[True])):
                batch = records[offset:offset + max(1, self.batch_sizes[True])]
                current = self.q(self.images([row[0] for row in batch]), t.tensor([row[1] for row in batch], dtype=t.float32, device=self.d))[2].float()
                future = self.target(self.images([row[3] for row in batch]), t.tensor([row[4] for row in batch], dtype=t.float32, device=self.d))[2].float()
                control = t.tensor([row[8] for row in batch], dtype=t.float32, device=self.d)
                estimated, disagreement = self.q.predict_with_uncertainty(current, control)
                mistake += float((estimated.float() - future).square().mean(dim=1).sum().item())
                disagreements += float(disagreement.float().sum().item())
                baseline += float((current - future).square().mean(dim=1).sum().item())
                examples += len(batch)
        if examples == 0 or not math.isfinite(mistake) or not math.isfinite(baseline) or baseline <= 1e-9:
            return None
        return (mistake + disagreements * .25) / baseline

    def calibrate_planning(self, records):
        ratio = self.dynamics_metric(records)
        self.planning_ratio = ratio
        self.planning_trust = max(0., min(1., 1. - ratio)) if ratio is not None and math.isfinite(ratio) else 0.
        return self.planning_trust

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

    def validation_targets(self, records):
        t = self.t
        labels = []
        self.q.eval()
        with t.no_grad():
            for start in range(0, len(records), 24):
                segment = records[start:start + 24]
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
        return labels

    def begin_sleep(self):
        with self.save_lock:
            records = list(self.memory)
        with self.model_lock:
            self.train_memory = None
            self.sampler_key = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None
            self.sleep_initial_capacity = (len(self.q.growing), self.growth_at_step, self.growth_attempts, len(self.q.world_models), self.world_growth_at_step, len(self.q.visual_growing), self.visual_growth_at_step)
            split = sleep_split(records)
            if split is None:
                self.train_memory = []
                return
            self.train_memory, validation, audit = split
            self.grow_from_evidence(self.train_memory)
            labels = self.validation_targets(validation)
            audit_labels = self.validation_targets(audit)
            self.sleep_audit = (audit, audit_labels, self.evaluate(audit, audit_labels), self.policy_metric(audit), self.effect_metric(audit), self.dynamics_metric(audit))
            before = self.evaluate(validation, labels)
            quality = self.policy_metric(validation)
            effect_before = self.effect_metric(validation)
            dynamics_before = self.dynamics_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads, effect_before, dynamics_before)
            return {'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'world_models': 2 + len(self.q.world_models), 'parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'expanded': any(step == self.steps and step > 0 for step in (self.growth_at_step, self.world_growth_at_step, self.visual_growth_at_step))}

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
            dynamics_before = self.sleep_evaluation[9]
            dynamics_after = self.dynamics_metric(records)
            dynamics_ok = dynamics_before is None or (dynamics_after is not None and math.isfinite(dynamics_after) and dynamics_after <= dynamics_before + max(1e-6, abs(dynamics_before) * .05))
            if effect_ok and dynamics_ok and math.isfinite(after) and after + tolerance < before and (quality is None or current is None or current + .025 >= quality):
                if self.sleep_best is None or after + tolerance < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.q.state_dict()), copy.deepcopy(self.target.state_dict()), copy.deepcopy(self.optq.state_dict()), self.grads)
            return after

    def rollback_sleep_capacity(self):
        initial = self.sleep_initial_capacity
        self.sleep_initial_capacity = None
        if initial is not None:
            if len(self.q.growing) != initial[0] or len(self.q.world_models) != initial[3] or len(self.q.visual_growing) != initial[5]:
                self.resize_capacity(initial[0], initial[3], initial[5])
            self.growth_at_step = initial[1]
            self.growth_attempts = initial[2]
            self.world_growth_at_step = initial[4]
            self.visual_growth_at_step = initial[6]

    def end_sleep(self):
        with self.model_lock:
            self.train_memory = None
            self.sampler_key = None
            if self.sleep_evaluation is None:
                self.rollback_sleep_capacity()
                return None
            after = self.sleep_progress()
            records, labels, before, quality, old_q, old_target, old_opt, old_grads, old_effect, old_dynamics = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            audit = self.sleep_audit
            self.sleep_audit = None
            current = self.policy_metric(records)
            if best is not None:
                self.q.load_state_dict(best[2])
                self.target.load_state_dict(best[3])
                self.optq.load_state_dict(best[4])
                self.grads = best[5]
                if audit is not None:
                    audit_rows, audit_targets, audit_before, audit_policy, audit_effect, audit_dynamics = audit
                    audit_after = self.evaluate(audit_rows, audit_targets)
                    audit_current = self.policy_metric(audit_rows)
                    audit_new_effect = self.effect_metric(audit_rows)
                    audit_new_dynamics = self.dynamics_metric(audit_rows)
                    tolerance = max(1e-6, abs(audit_before) * .02)
                    if not math.isfinite(audit_after) or audit_after > audit_before + tolerance or (audit_policy is not None and audit_current is not None and audit_current + .025 < audit_policy) or (audit_effect is not None and (audit_new_effect is None or audit_new_effect > audit_effect + max(1e-6, abs(audit_effect) * .02))) or (audit_dynamics is not None and (audit_new_dynamics is None or audit_new_dynamics > audit_dynamics + max(1e-6, abs(audit_dynamics) * .05))):
                        self.q.load_state_dict(old_q)
                        self.target.load_state_dict(old_target)
                        self.optq.load_state_dict(old_opt)
                        self.grads = old_grads
                        self.rollback_sleep_capacity()
                        self.calibrate_planning(audit_rows)
                        return False, before, audit_after, quality, audit_current
                self.sleep_initial_capacity = None
                self.calibrate_planning(audit[0] if audit is not None else records)
                return True, before, best[0], quality, best[1]
            self.q.load_state_dict(old_q)
            self.target.load_state_dict(old_target)
            self.optq.load_state_dict(old_opt)
            self.grads = old_grads
            self.rollback_sleep_capacity()
            if audit is not None:
                self.calibrate_planning(audit[0])
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
                    snapshot = {'version': 17, 'generation': generation, 'q': cpu_copy(self.q.state_dict()), 'target': cpu_copy(self.target.state_dict()), 'opt': cpu_copy(self.optq.state_dict()), 'steps': steps, 'grads': self.grads, 'replay_count': len(memory), 'capacity_depth': len(self.q.growing), 'capacity_visual_depth': len(self.q.visual_growing), 'capacity_world_models': len(self.q.world_models), 'growth_at_step': self.growth_at_step, 'growth_attempts': self.growth_attempts, 'world_growth_at_step': self.world_growth_at_step, 'visual_growth_at_step': self.visual_growth_at_step}
            path = self.folder / f'model.{model_slot}.pt'
            tmp = self.folder / f'model.{model_slot}.pt.tmp'
            try:
                with open(tmp, 'wb') as raw:
                    self.t.save(snapshot, raw)
                    raw.flush()
                    os.fsync(raw.fileno())
                save_replay(self.folder, memory, slot, generation)
                self.archive.sync()
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
        reconstruction = model.reconstruct(features)
        visual_target = torch.nn.functional.adaptive_avg_pool2d(frames, (8, 12)).flatten(1)
        predicted_features, disagreement = model.predict_with_uncertainty(features, controls)
        future_features = target(frames, meta)[2].detach()
        predicted_actions = model.infer_action(features, future_features)
        loss = torch.nn.functional.smooth_l1_loss(selected, expected) + .03 * (movement - controls).square().mean() + .2 * torch.nn.functional.smooth_l1_loss(observed, expected) + torch.nn.functional.smooth_l1_loss(reliability, torch.ones_like(reliability)) + torch.nn.functional.smooth_l1_loss(predicted_features, future_features) + disagreement.mean() * .1 + .2 * torch.nn.functional.cross_entropy(predicted_actions, actions) + torch.nn.functional.smooth_l1_loss(reconstruction, visual_target)
        if not bool(torch.isfinite(loss).item()):
            raise ValueError('实际模型计算产生非法数值')
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.)
        optimizer.step()
    model.eval()
    if engine.use_bfloat16 or engine.use_float16:
        model.train()
        optimizer.zero_grad(set_to_none=True)
        with engine.autocast():
            amp_logits, amp_controls, amp_features = model(frames, meta)
        amp_features = amp_features.float()
        amp_controls = amp_controls.float()
        amp_loss = (amp_logits.float().square().mean() + model.effect_value(amp_features, controls).square().mean() + model.execute_value(amp_features, controls).square().mean() + model.next_features(amp_features, controls).square().mean() + model.next_features_alternative(amp_features, controls).square().mean() + amp_controls.square().mean() + torch.nn.functional.smooth_l1_loss(model.reconstruct(amp_features), visual_target))
        if not bool(torch.isfinite(amp_loss).item()):
            raise ValueError('混合精度计算出现非有限误差')
        amp_loss.backward()
        optimizer.step()
        model.eval()
    with torch.no_grad():
        logits, predicted, features = model(frames, meta)
        if not bool(torch.isfinite(logits).all().item()) or not bool(torch.isfinite(predicted).all().item()) or not bool(torch.isfinite(model.effect_value(features, controls)).all().item()) or not bool(torch.isfinite(model.execute_value(features, controls)).all().item()) or not bool(torch.isfinite(model.next_features(features, controls)).all().item()) or not bool(torch.isfinite(model.next_features_alternative(features, controls)).all().item()) or not bool(torch.isfinite(model.infer_action(features, features)).all().item()) or not bool(torch.isfinite(model.reconstruct(features)).all().item()):
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
            if not torch.cuda.is_available():
                raise RuntimeError('PyTorch CUDA 设备未初始化')
            devices = [torch.device('cuda:' + str(i)) for i in range(torch.cuda.device_count())]
        elif backend == 'directml':
            directml = importlib.import_module('torch_directml')
            devices = [directml.device(i) for i in range(directml.device_count())]
        else:
            return False
        passed = False
        for device in devices:
            try:
                matrix = torch.randn((64, 64), device=device, requires_grad=True)
                result = (matrix @ matrix.transpose(0, 1)).square().mean()
                result.backward()
                if backend == 'cuda':
                    torch.cuda.synchronize(device)
                if not math.isfinite(float(result.detach().cpu())) or not bool(torch.isfinite(matrix.grad.detach().cpu()).all()):
                    raise RuntimeError('GPU 正向及反向计算产生非法数值')
                Path(folder).mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix='.gpu_check_', dir=folder) as test_folder:
                    instance = TorchBrain(Path(test_folder), torch, device, 'GPU 计算验证')
                    validate_network(torch, instance, device)
                    del instance
                passed = True
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
            if not torch.cuda.is_available():
                raise RuntimeError('当前 PyTorch CUDA 构建为 ' + str(torch.version.cuda) + '，驱动或 GPU 初始化未通过；NVIDIA 设备详情：' + str(nvidia_driver_info()[:1]))
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
                    batches, budget = payload if isinstance(payload, tuple) else (payload, None)
                    engine.interactive_budget = budget
                    trained = engine.train(batches, AnyStop(cancel_event, preempt_event))
                    result = (trained, engine.performance())
                elif operation == 'begin_sleep':
                    result = engine.begin_sleep()
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
                elif operation == 'sync_fast':
                    records, steps = payload
                    result = engine.restore_experience(records, steps, rebuild=False)
                elif operation == 'distill_policy':
                    result = engine.distill_policy(payload, AnyStop(cancel_event))
                elif operation == 'warm_train':
                    result = engine.train(payload, AnyStop(cancel_event, preempt_event))
                elif operation == 'append_records':
                    records, steps = payload
                    result = engine.append_experience(records, steps)
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
        if 'engine' in locals() and engine is not None:
            try:
                engine.archive.close()
            except (sqlite3.Error, OSError):
                pass
        channel.close()


class RemoteBrain:
    def __init__(self, folder, runtime, backend, cancel=None):
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
        self.inference_interval = 0.
        self.latest_perf = {}
        self.sleeping = False
        self.latest_capacity = None
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
            startup = time.monotonic()
            while not self.channel.poll(.15):
                if cancel is not None and cancel.is_set():
                    self.process.terminate()
                    raise InterruptedError('后端初始化已取消')
                if not self.process.is_alive():
                    raise RuntimeError('计算引擎在初始化期间退出')
                if time.monotonic() - startup > 100.:
                    self.process.terminate()
                    raise TimeoutError('计算引擎初始化超时')
            if cancel is not None and cancel.is_set():
                self.process.terminate()
                raise InterruptedError('后端初始化已取消')
            kind, value = self._receive(.2)
            if kind != 'ready':
                raise RuntimeError(str(value))
            self.label, self.steps, self.generation, count = value
            engine_generation = self.generation
            latest = newest_replay(folder)
            recovered = [latest] if latest is not None else []
            if recovered:
                generation, slot, records = recovered[0]
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

    def choose(self, ob, meta, held, targets=None):
        self.inference_pending.set()
        self.train_preempt.set()
        started = time.monotonic()
        interval = started - self.recent_inference
        if self.inference_interval <= 0.:
            self.inference_interval = interval
        else:
            self.inference_interval += (interval - self.inference_interval) / math.sqrt(1. + self.steps)
        try:
            return self._request('choose', (ob, meta, held, targets), timeout=15)
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
            budget = None if self.sleeping else max(self.recent_inference_cost, self.inference_interval * .35)
            result, perf = self._request('train', (batches, budget), timeout=max(45., batches * 3.))
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
        self.latest_capacity = self._request('begin_sleep')
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
            if not self.memory or self.memory[-1][6]:
                return
        self._request('mark_last_done', timeout=12)
        with self.save_lock:
            if self.memory and not self.memory[-1][6]:
                last = self.memory.pop()
                self.memory.append((*last[:6], True, *last[7:]))

    def sync(self, records, steps):
        entries = list(records)[-REPLAY_LIMIT:]
        count = max(int(steps), len(entries))
        self._request('sync', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def sync_fast(self, records, steps):
        entries = list(records)[-REPLAY_LIMIT:]
        count = max(int(steps), len(entries))
        self._request('sync_fast', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries, maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def distill_policy(self, samples, stop):
        if stop.is_set() or not samples:
            return 0
        return self._request('distill_policy', samples, timeout=120)

    def warm_train(self, batches, stop):
        if stop.is_set() or batches <= 0:
            return 0
        return self._request('warm_train', batches, timeout=120)

    def append_records(self, records, steps):
        entries = list(records)
        if not entries:
            return
        self._request('append_records', (entries, int(steps)), timeout=120)
        with self.save_lock:
            self.memory.extend(entries)
            self.steps = max(self.steps, int(steps), len(self.memory))

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
    u.EnumChildWindows.argtypes = (wintypes.HWND, WNDPROC, wintypes.LPARAM)
    u.IsWindowEnabled.argtypes = (wintypes.HWND,)
    u.IsWindowEnabled.restype = wintypes.BOOL
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
    u.GetCursorPos.restype = wintypes.BOOL
    u.GetSystemMetrics.argtypes = (ctypes.c_int,)
    u.GetSystemMetrics.restype = ctypes.c_int
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
    identity = ' '.join(title.strip().casefold().split())
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


def environment_for(folder, hwnd, display_name):
    descriptor = display_name.rsplit('  [0x', 1)[0].strip().casefold()
    descriptor = window_fingerprint(hwnd, descriptor)
    digest = hashlib.sha256(descriptor.encode('utf-8')).digest()
    code = tuple((int.from_bytes(digest[i:i + 4], 'little') / 4294967295.) * 2. - 1. for i in (0, 4))
    return Path(folder) / 'environments' / digest.hex()[:24], code


def send_mouse(flags, data=0, dx=0, dy=0):
    packet = INPUT()
    packet.type = 0
    packet.data.mi = MOUSEINPUT(int(dx), int(dy), ctypes.c_uint32(data).value, flags, 0, AI_INPUT_MARK)
    if u.SendInput(1, ctypes.byref(packet), ctypes.sizeof(INPUT)) != 1:
        raise OSError(ctypes.get_last_error(), 'Windows 拒绝鼠标输入；请检查目标窗口权限和桌面状态')


def send_cursor(px, py):
    left = u.GetSystemMetrics(76)
    top = u.GetSystemMetrics(77)
    width = u.GetSystemMetrics(78)
    height = u.GetSystemMetrics(79)
    if width <= 0 or height <= 0:
        raise RuntimeError('无法读取虚拟桌面边界')
    nx = round((px - left) * 65535 / max(1, width - 1))
    ny = round((py - top) * 65535 / max(1, height - 1))
    send_mouse(0x8001 | 0x4000, dx=max(0, min(65535, nx)), dy=max(0, min(65535, ny)))


def ensure_cursor(px, py, timeout, stop=None):
    deadline = time.monotonic() + timeout
    while True:
        if stop is not None and stop.is_set():
            raise InterruptedError('已停止鼠标控制')
        point = POINT()
        if u.GetCursorPos(ctypes.byref(point)) and abs(point.x - px) <= 2 and abs(point.y - py) <= 2:
            return
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError('Windows 没有执行鼠标定位指令；请检查桌面及目标窗口权限')
        time.sleep(min(.005, remaining))


class WindowsIO:
    def __init__(self, hwnd):
        self.hwnd = int(hwnd)
        self.window_pid = wintypes.DWORD()
        u.GetWindowThreadProcessId(self.hwnd, ctypes.byref(self.window_pid))
        self.target_scan_at = 0.
        self.target_region = None
        self.target_cache = ()
        self.io_lock = threading.RLock()
        self.keyboard_guard = None
        self.velocity = (0., 0.)
        self.grabber = None
        self.grabber_errors = 0
        self.capture_failures = {'wgc': 0, 'dxcam': 0, 'gdi': 0}
        self.scene_texture = None
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
        self.frozen_wgc = None
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

    def semantic_targets(self, region):
        now = time.monotonic()
        interval = max(.25, self.last_capture_ms / 1000. * math.sqrt(VIS_W * VIS_H))
        if self.target_region == region and now < self.target_scan_at:
            return self.target_cache
        x, y, width, height = region
        found = []
        def visit(child, extra):
            try:
                if not u.IsWindowVisible(child) or not u.IsWindowEnabled(child):
                    return True
                name = ctypes.create_unicode_buffer(256)
                u.GetClassNameW(child, name, len(name))
                category = name.value.casefold()
                if not any(tag in category for tag in ('button', 'edit', 'combo', 'listbox', 'listview', 'treeview', 'toolbar', 'trackbar', 'scrollbar', 'tabcontrol', 'link')):
                    return True
                box = RECT()
                if not u.GetWindowRect(child, ctypes.byref(box)):
                    return True
                left, right = max(x, box.left), min(x + width, box.right)
                top, bottom = max(y, box.top), min(y + height, box.bottom)
                if right <= left or bottom <= top:
                    return True
                center_x, center_y = (left + right) / 2, (top + bottom) / 2
                if x + 3 < center_x < x + width - 3 and y + 3 < center_y < y + height - 3:
                    found.append(((center_x - x) / width, (center_y - y) / height, 2 if 'button' in category or 'link' in category else 1))
            except (OSError, ValueError):
                pass
            return True
        callback = WNDPROC(visit)
        u.EnumChildWindows(self.hwnd, callback, 0)
        self.target_cache = tuple(found)
        self.target_region = region
        self.target_scan_at = now + interval
        return self.target_cache

    def cursor(self):
        p = POINT()
        if not u.GetCursorPos(ctypes.byref(p)):
            raise OSError('无法读取鼠标位置')
        return (p.x, p.y)

    def keys(self):
        return {k: bool(u.GetAsyncKeyState(v) & 0x8000) for k, v in (('l', 1), ('r', 2), ('m', 4))}

    def keyboard_activity(self):
        return any(u.GetAsyncKeyState(key) & 0x8000 for key in range(8, 255))

    def captured(self, content, backend, stamp, frame_id=None):
        self.capture_metadata.append((backend, stamp, frame_id))
        return content

    def capture(self, x, y, w, h, force_gdi=False):
        if not force_gdi and self.wgc is not None:
            try:
                if self.frozen_wgc is not None:
                    image, stamp, frame_id = self.frozen_wgc
                else:
                    with self.wgc_lock:
                        image, stamp, frame_id = self.wgc_frame, self.wgc_stamp, self.wgc_frame_id
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
                self.capture_failures['wgc'] += 1
        if not force_gdi and self.grabber is not None and self.grabber_errors < max(3, int(math.sqrt(max(1, self.capture_epoch + 1)))):
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
                self.capture_failures['dxcam'] += 1
        if not g.StretchBlt(self.mem, 0, 0, VIS_W, VIS_H, self.src, x, y, w, h, 0x00CC0020):
            self.capture_failures['gdi'] += 1
            raise OSError('画面获取失败')
        raw = ctypes.string_at(self.ptr, PIXELS * 4)
        return self.captured(raw[2::4] + raw[1::4] + raw[0::4], 'gdi', time.monotonic())

    def image(self, region):
        capture_start = time.monotonic()
        self.capture_metadata = []
        x, y, w, h = region
        px, py = self.cursor()
        with self.wgc_lock:
            self.frozen_wgc = (self.wgc_frame, self.wgc_stamp, self.wgc_frame_id)
        try:
            overview = self.capture(x, y, w, h)
            unit = PIXELS
            dx = max(1, VIS_W // max(1, int(math.sqrt(VIS_W))))
            dy = max(1, VIS_H // max(1, int(math.sqrt(VIS_H))))
            contrasts = []
            for row in range(dy, VIS_H - dy, dy):
                for col in range(dx, VIS_W - dx, dx):
                    at = row * VIS_W + col
                    across = at + dx
                    below = at + dy * VIS_W
                    contrasts.append(sum(abs(overview[at + c * unit] - overview[across + c * unit]) + abs(overview[at + c * unit] - overview[below + c * unit]) for c in range(CHANNELS)))
            texture = sum(contrasts) / max(1, len(contrasts))
            if self.scene_texture is None:
                self.scene_texture = texture
            else:
                self.scene_texture += (texture - self.scene_texture) / max(1., math.sqrt(1. + self.capture_epoch + len(self.wgc_periods)))
            base = math.sqrt(PIXELS / max(1, w * h))
            complexity = texture / max(1., self.scene_texture)
            focus = max(base, min(1., base * (1. + complexity)))
            zoom_w = max(min(w, VIS_W), min(w, int(round(w * focus))))
            zoom_h = max(1, min(h, int(round(zoom_w * VIS_H / VIS_W))))
            if zoom_h == h and h * VIS_W < zoom_w * VIS_H:
                zoom_w = max(1, min(w, int(round(zoom_h * VIS_W / VIS_H))))
            crop_x = max(x, min(x + w - zoom_w, px - zoom_w // 2))
            crop_y = max(y, min(y + h - zoom_h, py - zoom_h // 2))
            result = overview + self.capture(crop_x, crop_y, zoom_w, zoom_h)
            if len(self.capture_metadata) != 2 or self.capture_metadata[0][0] != self.capture_metadata[1][0]:
                self.capture_metadata.clear()
                result = self.capture(x, y, w, h, force_gdi=True) + self.capture(crop_x, crop_y, zoom_w, zoom_h, force_gdi=True)
        finally:
            self.frozen_wgc = None
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
        if self.keyboard_guard is not None and not self.keyboard_guard.is_set():
            raise RuntimeError('键盘急停监控暂不可用，禁止发送鼠标指令')
        if stop.is_set() or self.halted.is_set():
            raise InterruptedError('键盘急停')
        if not self.foreground() or self.region() != region:
            raise RuntimeError('目标窗口暂不可操作，等待恢复')
        if require_pointer:
            x, y, w, h = region
            px, py = self.cursor()
            if not (x + 3 <= px < x + w - 3 and y + 3 <= py < y + h - 3) or not self.pointer_on_target(px, py):
                raise RuntimeError('光标暂不在目标客户区，正在重新定位')

    def prepare_cursor(self, region, stop):
        with self.io_lock:
            self.safe(region, stop, False)
            x, y, w, h = region
            px, py = self.cursor()
            if not (x + 3 <= px < x + w - 3 and y + 3 <= py < y + h - 3) or not self.pointer_on_target(px, py):
                self.safe(region, stop, False)
                send_cursor(x + w // 2, y + h // 2)
                ensure_cursor(x + w // 2, y + h // 2, .2, stop)
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
                self.velocity = (0., 0.)
                self.last_ai_cursor = (px, py)
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
                send_cursor(nx, ny)
                ensure_cursor(nx, ny, max(.03, min(.2, dt + self.last_capture_ms / 1000.)), stop)
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
            try:
                self.release()
                release_error = None
            except Exception as retry_error:
                release_error = retry_error
        if self.wgc_control is not None:
            try:
                self.wgc_control.stop()
            except Exception:
                pass
            finally:
                self.wgc_control = None
                self.wgc = None
                with self.wgc_lock:
                    self.wgc_frame = None
                    self.frozen_wgc = None
        if self.grabber is not None:
            try:
                self.grabber.stop()
                if hasattr(self.grabber, 'release'):
                    self.grabber.release()
            except (AttributeError, OSError, RuntimeError):
                pass
            finally:
                self.grabber = None
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
    probe_file = None
    try:
        Path(folder).mkdir(parents=True, exist_ok=True)
        probe_file = Path(folder) / ('.probe_' + os.urandom(6).hex() + '.log')
        cmd = [sys.executable, str(Path(__file__).resolve()), '--mouseai-hardware-probe', backend, str(folder)]
        with open(probe_file, 'wb') as stream:
            proc = managed_process(cmd, env=env, stdout=stream, stderr=subprocess.STDOUT, creationflags=creation)
            started = time.monotonic()
            while proc.poll() is None:
                if cancel is not None and cancel.is_set():
                    stop_process_tree(proc)
                    return False
                if time.monotonic() - started > 100:
                    stop_process_tree(proc)
                    if report is not None:
                        report(backend + ' 后端测试超时，已取消当前测试')
                    return False
                time.sleep(.1)
        lines = probe_file.read_text(encoding='utf-8', errors='replace').splitlines()
        passed = proc.returncode == 0 and any(line.strip() == 'READY' for line in lines)
        if not passed and report is not None:
            detail = [line for line in lines if line.strip()]
            report(backend + ' 检测未通过' + ('：' + detail[-1][:180] if detail else ''))
        return passed
    except (OSError, subprocess.SubprocessError) as error:
        if report is not None:
            report(backend + ' 检测中断：' + str(error)[:150])
        return False
    finally:
        if proc is not None:
            if proc.poll() is None:
                stop_process_tree(proc)
            else:
                release_process(proc)
        if probe_file is not None:
            try:
                probe_file.unlink(missing_ok=True)
            except OSError:
                pass


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
    diagnostic = folder / ('.installation_' + re.sub(r'[^a-zA-Z0-9_.-]', '_', backend) + '.log')
    succeeded = False
    proc = None
    try:
        with open(staging / 'install.log', 'wb') as log:
            proc = managed_process(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, creationflags=creation)
            started = time.monotonic()
            while proc.poll() is None:
                if cancel.is_set() or time.monotonic() - started > 600:
                    stop_process_tree(proc)
                    report(backend + ' 配置取消或超时，保留之前的计算组件')
                    return False
                time.sleep(.15)
        if proc.returncode != 0:
            lines = (staging / 'install.log').read_text(encoding='utf-8', errors='replace').strip().splitlines()
            report(backend + ' 安装失败' + ('：' + lines[-1][:180] if lines else ''))
            return False
        if backend.startswith('cuda_') and not (packages / 'torch').is_dir():
            report('CUDA 安装结果不完整，未替换现有计算组件')
            return False
        if backend == 'directml' and not (packages / 'torch_directml').exists():
            report('DirectML 安装结果不完整，未替换现有计算组件')
            return False
        if backend == 'cpu' and not (packages / 'torch').is_dir():
            report('CPU 深度学习组件安装不完整，继续使用基础学习引擎')
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
        succeeded = True
        return True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report(backend + ' 配置异常：' + str(error)[:160])
        return False
    finally:
        if proc is not None:
            if proc.poll() is None:
                stop_process_tree(proc)
            else:
                release_process(proc)
        try:
            log = staging / 'install.log'
            if succeeded:
                diagnostic.unlink(missing_ok=True)
            elif log.exists():
                shutil.copyfile(log, diagnostic)
                report(backend + ' 的安装日志已保存在数据文件夹')
        except OSError:
            pass
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


def available_cuda_wheels(driver, cancel=None, runtime_folder=None):
    if cancel is not None and cancel.is_set():
        return []
    cache = Path(runtime_folder) / '.cuda_catalog.gz' if runtime_folder is not None else None
    tag = 'cp' + str(sys.version_info.major) + str(sys.version_info.minor)
    driver_key = list(driver) if driver is not None else None
    if cache is not None:
        saved = read_json(cache, {})
        if isinstance(saved, dict) and saved.get('driver') == driver_key and saved.get('python') == tag and isinstance(saved.get('when'), (int, float)) and time.time() - saved['when'] < 86400:
            values = saved.get('wheels')
            if isinstance(values, list) and values and all(isinstance(v, str) and re.fullmatch(r'cu\d{3,4}', v) for v in values):
                return values
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
    supported = []
    for wheel in versions:
        if cancel is not None and cancel.is_set():
            return supported
        try:
            with urllib.request.urlopen('https://download.pytorch.org/whl/' + wheel + '/torch/', timeout=8) as response:
                listing = html.unescape(urllib.parse.unquote(response.read(16000000).decode('utf-8', errors='replace').lower()))
            filenames = re.findall(r'torch-[^<>"\s/]+?\.whl', listing)
            if any(re.search(r'-' + tag + r'-' + tag + r'-win_amd64\.whl$', name) for name in filenames):
                supported.append(wheel)
        except (OSError, ValueError, TimeoutError):
            continue
    if cache is not None and supported:
        try:
            save_json(cache, {'when': time.time(), 'python': tag, 'driver': driver_key, 'wheels': supported})
        except (OSError, ValueError, TypeError):
            pass
    return supported


def load_brain(folder, report, cancel, runtime_folder=None, gpu_only=False):
    folder.mkdir(parents=True, exist_ok=True)
    runtime_folder = Path(runtime_folder) if runtime_folder is not None else folder
    runtime_folder.mkdir(parents=True, exist_ok=True)
    cache = runtime_folder / '.cache'
    cache.mkdir(parents=True, exist_ok=True)
    for key in ('TEMP', 'TMP', 'TMPDIR', 'XDG_CACHE_HOME', 'TORCH_HOME', 'CUDA_CACHE_PATH', 'TORCHINDUCTOR_CACHE_DIR', 'TRITON_CACHE_DIR', 'PIP_CACHE_DIR', 'NUMBA_CACHE_DIR'):
        os.environ[key] = str(cache)
    gpus = detect_gpu()
    nvidia = any('nvidia' in name.lower() for name in gpus)
    device_fingerprint = hashlib.blake2s(('|'.join(gpus) + str(nvidia_driver_info()) + sys.version + sys.executable).encode('utf-8', errors='replace'), digest_size=10).hexdigest() if os.name == 'nt' else ''
    if gpus:
        report('识别的图形设备：' + '、'.join(gpus[:4]))
    if os.name == 'nt' and not nvidia and nvidia_driver_info():
        nvidia = True
        gpus.append('NVIDIA GPU')
    cuda_runtimes = sorted((path for path in runtime_folder.glob('.runtime_cuda_cu*') if (path / 'torch').is_dir()), reverse=True)
    directml_runtime = runtime_folder / '.runtime_directml'
    cpu_runtime = runtime_folder / '.runtime_cpu'
    preference = read_json(runtime_folder / '.backend_preference.gz', {})
    if not isinstance(preference, dict):
        preference = {}
    preferred_runtime = preference.get('runtime')
    if preference.get('backend') == 'cuda' and isinstance(preferred_runtime, str):
        match = next((path for path in cuda_runtimes if path.name == preferred_runtime), None)
        if match is not None and preference.get('fingerprint') == device_fingerprint:
            cuda_runtimes.remove(match)
            cuda_runtimes.insert(0, match)
    if os.name == 'nt' and not cancel.is_set():
        tried = set()
        failures = []
        def launch(runtime, backend):
            key = (str(runtime) if runtime is not None else '', backend)
            if key in tried or cancel.is_set():
                return None
            tried.add(key)
            try:
                ready = RemoteBrain(folder, runtime, backend, cancel)
                if backend in ('cuda', 'directml'):
                    try:
                        save_json(runtime_folder / '.backend_preference.gz', {'backend': backend, 'runtime': runtime.name if runtime is not None else '', 'fingerprint': device_fingerprint, 'verified_at': time.time()})
                    except (OSError, ValueError):
                        pass
                return ready
            except Exception as error:
                detail = backend + ' (' + (runtime.name if runtime else '系统运行时') + ')：' + str(error)[:180]
                failures.append(detail)
                if not cancel.is_set():
                    report('计算引擎验证失败：' + detail[:150])
                return None
        cuda_candidates = ([None, *cuda_runtimes] if preference.get('backend') == 'cuda' and preferred_runtime == '' and preference.get('fingerprint') == device_fingerprint else [*cuda_runtimes, None]) if nvidia or cuda_runtimes else []
        for runtime in cuda_candidates:
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
            wheels = available_cuda_wheels(driver, cancel, runtime_folder)
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
        directml_candidates = ([directml_runtime, None] if directml_runtime.exists() else [None]) if gpus or directml_runtime.exists() else []
        for runtime in directml_candidates:
            ready = launch(runtime, 'directml')
            if ready is not None:
                return ready
        if gpus and not cancel.is_set() and not (directml_runtime / 'torch_directml').exists():
            if install_package(runtime_folder, ['torch-directml'], report, cancel, 'directml'):
                ready = launch(directml_runtime, 'directml')
                if ready is not None:
                    return ready
    if gpus and not cancel.is_set():
        try:
            save_json(runtime_folder / '.hardware_diagnostics.gz', {'when': time.time(), 'devices': gpus, 'failures': failures if os.name == 'nt' else [], 'python': sys.version, 'cuda_driver': cuda_driver_version(), 'fingerprint': device_fingerprint})
        except (OSError, ValueError):
            pass
        report('已发现显卡，但 CUDA/DirectML 的实际模型计算未通过；诊断已保存在所选文件夹，暂由 CPU 运行')
    if gpu_only:
        return None
    if cancel.is_set():
        return None
    runtimes = [cpu_runtime] if (cpu_runtime / 'torch').exists() else []
    runtimes.append(None)
    for runtime in runtimes:
        try:
            return RemoteBrain(folder, runtime, 'cpu', cancel)
        except Exception as error:
            report('CPU 深度学习后端初始化失败：' + str(error)[:120])
    marker = runtime_folder / '.cpu_install_attempt'
    memory = available_memory()
    can_install = not memory or memory > VIS_N * REPLAY_LIMIT * 3
    try:
        previous = marker.stat().st_mtime if marker.exists() else 0.
        if can_install and time.time() - previous > 86400 and not cancel.is_set():
            marker.touch()
            if install_package(runtime_folder, ['--only-binary=:all:', '--index-url', 'https://download.pytorch.org/whl/cpu', 'torch'], report, cancel, 'cpu'):
                return RemoteBrain(folder, cpu_runtime, 'cpu', cancel)
    except (OSError, RuntimeError, ValueError) as error:
        report('CPU 深度学习后端配置未完成：' + str(error)[:120])
    return None

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
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        self.root.geometry(f'{min(940, max(620, screen_width - 80))}x{min(700, max(520, screen_height - 100))}')
        self.root.minsize(min(700, screen_width), min(540, screen_height))
        home = Path.home()
        self.folder = (home / 'Documents' / 'MouseAI') if (home / 'Documents').exists() else (home / 'MouseAI')
        self.control_stop = threading.Event()
        self.online_stop = threading.Event()
        self.online_worker = None
        self.online_error = None
        self.active_io = None
        self.release_worker = None
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
        self.keyboard_alive_at = 0.
        self.control_worker = None
        self.control_heartbeat = 0.
        self.watchdog_limit = 3.
        self.close_started = 0.
        self.saver = None
        self.capture_worker = None
        self.acceleration_lock = threading.Lock()
        self.acceleration_thread = None
        self.acceleration_stop = threading.Event()
        self.acceleration_ready = None
        self.acceleration_folder = None
        self.acceleration_attempt_folder = None
        self.exit_backup = None
        self.shutdown_worker = None
        self.acceleration_cleanup = None
        self.exit_backup_error = None
        self.last_checkpoint_step = 0
        self.last_checkpoint_time = time.monotonic()
        self.last_checkpoint_duration = 0.
        self.control_history = deque(maxlen=max(4, int(math.sqrt(REPLAY_LIMIT))))
        self.next_backend_retry = 0.
        self.backend_faults = {}
        self.brain = None
        self.brain_folder = None
        self.goal_atlas = None
        self.mode = 'idle'
        self.switching_folder = False
        self.message = queue.Queue()
        self.fast_messages = {}
        self.fast_messages_lock = threading.Lock()
        self.listing = {}
        self.iterations = 0
        self.backend = tk.StringVar(value='未启动')
        self.folder_text = tk.StringVar(value=str(self.folder))
        self.status = tk.StringVar(value='选择目标窗口，点击绿色按钮开始')
        self.phase = tk.StringVar(value='空闲')
        self.progress_value = tk.DoubleVar(value=0.)
        self.progress_text = tk.StringVar(value='准备状态 · 0%')
        self.buttons = {}
        self.issue = tk.StringVar(value='无')
        self.statistics = tk.StringVar(value='经验 0 条 · 实际操作 0 次 · 可控进展待观测（非任务成功率）')
        self.capture_text = tk.StringVar(value='等待首次画面 · 检查截图来源')
        self.goal_text = tk.StringVar(value='等待观察 · 尚未建立状态目标')
        self.safety_text = tk.StringVar(value='键盘急停监控正在启动')
        self.control_details = tk.StringVar(value='鼠标未控制 · 左键释放 · 右键释放 · 中键释放 · 滚轮停止')
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
        self.key_thread = threading.Thread(target=self.keyboard_supervisor, daemon=True)
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
        tk.Label(self.root, text='窗口鼠标 AI', bg='#10131a', fg='#f2f5fa', font=('Microsoft YaHei UI', 22, 'bold')).pack(anchor='w', padx=24, pady=(18, 10))
        selector = tk.Frame(self.root, bg='#10131a')
        selector.pack(fill='x', padx=24)
        tk.Label(selector, text='控制哪个窗口', bg='#10131a', fg='#d9e0ea', font=('Microsoft YaHei UI', 10)).pack(anchor='w', pady=(0, 6))
        selection = tk.Frame(selector, bg='#10131a')
        selection.pack(fill='x')
        self.combo = ttk.Combobox(selection, textvariable=self.combo_var, state='readonly', style='AI.TCombobox', font=('Microsoft YaHei UI', 10))
        self.combo.pack(side='left', fill='x', expand=True, ipady=4)
        self.combo.bind('<<ComboboxSelected>>', lambda event: self.status.set('目标窗口已选择，可以开始控制'))
        tk.Button(selection, text='刷新窗口', command=self.refresh, bg='#303949', fg='white', relief='flat', cursor='hand2', font=('Microsoft YaHei UI', 10), padx=14, pady=9).pack(side='left', padx=(10, 0))
        controls = tk.Frame(self.root, bg='#10131a')
        controls.pack(fill='x', padx=20, pady=(15, 14))
        for title, color, command in [('绿色 · 开始', '#18ad65', self.start), ('黑色 · 睡觉', '#262933', self.sleep), ('白色 · 唤醒', '#f1f4f8', self.wake), ('红色 · 退出', '#dc454e', self.close)]:
            fg = '#19222d' if color == '#f1f4f8' else '#ffffff'
            button = tk.Button(controls, text=title, command=command, bg=color, fg=fg, activebackground=color, activeforeground=fg, font=('Microsoft YaHei UI', 10, 'bold'), relief='flat', bd=0, pady=12, cursor='hand2')
            button.pack(side='left', fill='x', expand=True, padx=4)
            self.buttons[title[:2]] = button
        panel = tk.Frame(self.root, bg='#202631', padx=16, pady=12)
        panel.pack(fill='both', expand=True, padx=24)
        top = tk.Frame(panel, bg='#202631')
        top.pack(fill='x')
        tk.Label(top, text='当前阶段', bg='#202631', fg='#9aaac0', font=('Microsoft YaHei UI', 9)).pack(side='left')
        tk.Label(top, textvariable=self.phase, bg='#202631', fg='#69cfbd', font=('Microsoft YaHei UI', 12, 'bold')).pack(side='left', padx=(15, 0))
        status_label = tk.Label(panel, textvariable=self.status, bg='#202631', fg='#e0e8f2', anchor='w', justify='left', font=('Microsoft YaHei UI', 10))
        status_label.pack(fill='x', pady=(10, 12))
        progress_row = tk.Frame(panel, bg='#202631')
        progress_row.pack(fill='x', pady=(0, 5))
        tk.Label(progress_row, text='当前任务进度', bg='#202631', fg='#9aaac0', font=('Microsoft YaHei UI', 9)).pack(side='left')
        tk.Label(progress_row, textvariable=self.progress_text, bg='#202631', fg='#69cfbd', font=('Microsoft YaHei UI', 9, 'bold')).pack(side='right')
        sty.configure('AI.Horizontal.TProgressbar', troughcolor='#10131a', background='#18ad65', borderwidth=0, thickness=12)
        self.progress_bar = ttk.Progressbar(panel, variable=self.progress_value, maximum=100, mode='determinate', style='AI.Horizontal.TProgressbar')
        self.progress_bar.pack(fill='x', pady=(0, 12))
        tk.Frame(panel, bg='#343e4e', height=1).pack(fill='x')
        detail_labels = []
        for label, var, color in [('鼠标动作', self.control_details, '#d7e6ff'), ('学习情况', self.statistics, '#b0c0d4'), ('自主目标', self.goal_text, '#69cfbd'), ('计算设备', self.backend, '#69cfbd'), ('画面采集', self.capture_text, '#b0c0d4'), ('键盘安全', self.safety_text, '#69cfbd'), ('最近一次异常', self.issue, '#ffbb85')]:
            block = tk.Frame(panel, bg='#202631')
            block.pack(fill='x', pady=(9, 2))
            tk.Label(block, text=label, bg='#202631', fg='#8c9bb0', width=12, anchor='w', font=('Microsoft YaHei UI', 9)).pack(side='left', anchor='n')
            detail = tk.Label(block, textvariable=var, bg='#202631', fg=color, anchor='w', justify='left', font=('Microsoft YaHei UI', 9))
            detail.pack(side='left', fill='x', expand=True)
            detail_labels.append(detail)
        def resize_details(event):
            status_label.configure(wraplength=max(180, event.width - 30))
            for detail in detail_labels:
                detail.configure(wraplength=max(160, event.width - 150))
        panel.bind('<Configure>', resize_details)
        footer = tk.Frame(self.root, bg='#10131a')
        footer.pack(fill='x', padx=24, pady=(12, 0))
        self.folder_button = tk.Button(footer, text='选择数据文件夹', command=self.choose_folder, bg='#303949', fg='#f5f7fa', relief='flat', padx=12, pady=8, cursor='hand2')
        self.folder_button.pack(side='left')
        tk.Label(footer, textvariable=self.folder_text, bg='#10131a', fg='#8793a7', anchor='w', font=('Microsoft YaHei UI', 9)).pack(side='left', fill='x', expand=True, padx=(10, 0))
        tk.Label(self.root, text='控制时按下任意键，立即释放鼠标并停止', bg='#10131a', fg='#ffbb85', font=('Microsoft YaHei UI', 10)).pack(anchor='w', padx=24, pady=(10, 12))

    def update_buttons(self):
        available = self.mode == 'idle' and not self.switching_folder
        for name, valid in (('绿色', available), ('黑色', available), ('白色', self.mode == 'sleep'), ('红色', self.mode != 'closed')):
            control = self.buttons.get(name[:2])
            if control is not None:
                control.configure(state='normal' if valid else 'disabled')
        self.folder_button.configure(state='normal' if available else 'disabled')

    def set_progress(self, fraction, stage):
        percent = min(100., max(0., float(fraction)))
        self.progress_value.set(percent)
        self.progress_text.set(f'{stage} · {percent:.0f}%')

    def post(self, kind, value):
        if kind in ('control', 'stats', 'capture', 'accelerator', 'status', 'goal'):
            with self.fast_messages_lock:
                self.fast_messages[kind] = value
        else:
            self.message.put((kind, value))

    def pump(self):
        latest_control = None
        had_error = False
        for _ in range(max(16, int(math.sqrt(REPLAY_LIMIT)) * 2)):
            try:
                kind, val = self.message.get_nowait()
            except queue.Empty:
                break
            if kind == 'phase':
                self.phase.set(val)
            elif kind == 'backend':
                self.backend.set(val)
            elif kind == 'progress':
                self.set_progress(*val)
            elif kind == 'folder_changed':
                folder = Path(val)
                self.folder = folder
                self.data_folder = folder
                self.folder_text.set(str(folder))
                self.backend.set('未启动')
                self.issue.set('无')
                self.phase.set('空闲')
                self.status.set('已切换数据目录，旧数据保存完成')
                self.switching_folder = False
                self.mode = 'idle'
                self.set_progress(100, '文件夹切换完成')
            elif kind == 'folder_failed':
                self.set_progress(100, '文件夹切换结束 · 失败')
                self.switching_folder = False
                self.mode = 'idle'
                self.issue.set(str(val))
                self.status.set('切换文件夹失败：' + str(val))
                self.phase.set('需要检查')
            elif kind == 'done':
                if self.mode != 'closed' and val == self.mode:
                    self.mode = 'idle'
                    self.phase.set('空闲')
                    if val == 'control':
                        self.set_progress(100, '本轮控制已结束')
                    elif val == 'sleep':
                        self.set_progress(100, '本轮睡眠已结束')
            elif kind == 'error':
                had_error = True
                self.issue.set(val)
                self.phase.set('异常')
                self.status.set('发生问题：' + val)
        with self.fast_messages_lock:
            updates = self.fast_messages
            self.fast_messages = {}
        if 'status' in updates and not had_error and self.mode != 'closed':
            self.status.set(updates['status'])
        if 'stats' in updates:
            self.statistics.set(updates['stats'])
        if 'capture' in updates:
            self.capture_text.set(updates['capture'])
        if 'goal' in updates:
            self.goal_text.set(updates['goal'])
        if 'accelerator' in updates and self.brain is not None and not self.brain.accelerated and self.mode != 'closed':
            self.backend.set(self.brain.label + ' · ' + str(updates['accelerator'])[:105])
        if 'control' in updates:
            latest_control = updates['control']
        if latest_control is not None:
            self.control_details.set(latest_control)
        if os.name == 'nt':
            healthy = self.keyboard_ready.is_set() and self.keyboard_alive_at and time.monotonic() - self.keyboard_alive_at < max(1., self.watchdog_limit)
            self.safety_text.set('键盘急停在线 · 任意按键停止鼠标控制' if healthy else '键盘急停暂停 · 正在自动恢复，禁止动作')
            if self.mode == 'control' and not healthy:
                self.status.set('键盘监控正在恢复；暂停鼠标操作')
        if not self.exit_stop.is_set():
            self.update_buttons()
            self.root.after(10 if not self.message.empty() else 90, self.pump)

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
        if self.mode != 'idle' or self.switching_folder:
            self.status.set('请先停止运行后再更换数据文件夹')
            return
        new = filedialog.askdirectory(parent=self.root, initialdir=str(self.folder), title='选择 AI 数据存放文件夹')
        if not new:
            return
        folder = Path(new)
        if folder == self.folder:
            return
        if any(worker is not None and worker.is_alive() for worker in (self.worker, self.online_worker)):
            self.status.set('控制线程仍在退出，请稍后更换目录')
            return
        self.switching_folder = True
        self.mode = 'switching'
        self.phase.set('保存并切换文件夹')
        self.status.set('正在后台保存旧数据，界面保持响应')
        self.set_progress(0, '切换文件夹')
        self.update_buttons()
        def transition():
            try:
                self.cancel_acceleration()
                for task in (self.acceleration_thread, self.capture_worker):
                    if task is not None and task.is_alive() and task is not threading.current_thread():
                        task.join()
                self.post('progress', (20, '释放旧计算资源'))
                if self.saver is not None and self.saver.is_alive():
                    self.saver.join()
                if self.exit_stop.is_set():
                    return
                previous = self.brain
                if previous is not None:
                    previous.save()
                    self.post('progress', (75, '模型已安全保存'))
                    previous.close()
                if self.exit_stop.is_set():
                    return
                self.brain = None
                self.brain_folder = None
                self.acceleration_attempt_folder = None
                self.next_backend_retry = 0.
                self.backend_faults = {}
                self.audit_sum = 0.
                self.audit_samples = 0
                self.post('folder_changed', str(folder))
            except Exception as error:
                self.post('folder_failed', str(error)[:170])
        self.worker = threading.Thread(target=transition, daemon=True)
        self.worker.start()

    def cancel_acceleration(self):
        self.acceleration_stop.set()
        with self.acceleration_lock:
            staged = self.acceleration_ready
            self.acceleration_ready = None
            self.acceleration_folder = None
            self.acceleration_attempt_folder = None
        if staged is not None:
            staged.close()

    def start_acceleration(self):
        if os.name != 'nt' or self.exit_stop.is_set() or self.brain is None or self.brain.accelerated:
            return
        if isinstance(self.brain, RemoteBrain) and not detect_gpu():
            return
        folder = self.data_folder
        with self.acceleration_lock:
            if self.acceleration_ready is not None and self.acceleration_folder == folder:
                return
            if self.acceleration_thread is not None and self.acceleration_thread.is_alive() and self.acceleration_folder == folder:
                return
            if self.acceleration_attempt_folder == folder and time.monotonic() < self.next_backend_retry:
                return
            self.acceleration_stop.set()
            token = threading.Event()
            self.acceleration_stop = token
            self.acceleration_folder = folder
            self.acceleration_attempt_folder = folder
            runtime_folder = self.folder

        def prepare():
            ready = None
            try:
                cancel = AnyStop(self.exit_stop, token)
                self.post('accelerator', '正在后台匹配 GPU，鼠标控制无需等待')
                ready = load_brain(folder, lambda msg: self.post('accelerator', msg), cancel, runtime_folder=runtime_folder, gpu_only=False)
                may_upgrade = isinstance(self.brain, LiteBrain) or (isinstance(self.brain, RemoteBrain) and not self.brain.accelerated and ready is not None and ready.accelerated)
                if ready is not None and not cancel.is_set() and self.brain_folder == folder and may_upgrade:
                    with self.brain.save_lock:
                        rows = list(self.brain.memory)
                        steps = self.brain.steps
                        generation = self.brain.generation
                    if generation > ready.generation or (generation == ready.generation and (steps > ready.steps or len(rows) > len(ready.memory))):
                        self.post('accelerator', 'GPU 已通过验证，正在后台同步交互经验')
                        ready.sync_fast(rows, steps)
                    if rows and not cancel.is_set() and isinstance(self.brain, LiteBrain):
                        with self.brain.save_lock:
                            eligible = [row for row in rows if not row[12]]
                            max_samples = max(1, int(math.sqrt(len(eligible)) * math.sqrt(max(1, os.cpu_count() or 1))))
                            selected = random.sample(eligible, min(len(eligible), max_samples))
                            samples = [(row[0], row[1], values) for row in selected if (values := self.brain.values(row[0], row[1])) is not None]
                        if samples and not cancel.is_set():
                            self.post('accelerator', 'GPU 正在学习轻量模型已经掌握的操作偏好')
                            try:
                                migrated = ready.distill_policy(samples, cancel)
                                self.post('accelerator', f'GPU 已训练迁移 {migrated} 条策略样本')
                            except Exception as migration_error:
                                self.post('accelerator', 'GPU 策略迁移验证未通过，仍保留已同步经验：' + str(migration_error)[:70])
                    available = sum(not row[12] for row in rows)
                    if available >= 2 and not cancel.is_set():
                        iterations = max(1, min(int(math.sqrt(available)), (os.cpu_count() or 1) * 2))
                        self.post('accelerator', f'深度学习引擎正在后台预训练交互经验（{iterations} 批）')
                        try:
                            trained = ready.warm_train(iterations, cancel)
                            self.post('accelerator', f'深度学习引擎已完成 {trained} 批训练，准备接管推理')
                        except Exception as warm_error:
                            self.post('accelerator', 'GPU 预训练尚未完成：' + str(warm_error)[:75])
                if ready is None and not cancel.is_set():
                    self.post('accelerator', '高级计算引擎尚未通过验证，基础学习仍可继续')
            except Exception as error:
                if ready is not None:
                    ready.close()
                    ready = None
                if not token.is_set() and not self.exit_stop.is_set():
                    self.post('accelerator', 'GPU 准备遇到问题：' + str(error)[:95])
            finally:
                with self.acceleration_lock:
                    valid = not token.is_set() and not self.exit_stop.is_set() and self.acceleration_folder == folder and self.acceleration_stop is token
                    if valid and ready is not None and self.acceleration_ready is None:
                        self.acceleration_ready = ready
                        self.post('accelerator', ready.label + ' 已就绪，正在等待安全切换')
                        ready = None
                    elif valid and ready is None:
                        self.next_backend_retry = time.monotonic() + math.sqrt(max(1, REPLAY_LIMIT))
                if ready is not None:
                    ready.close()

        self.acceleration_thread = threading.Thread(target=prepare, daemon=True)
        self.acceleration_thread.start()

    def upgrade_backend(self, io=None):
        with self.acceleration_lock:
            candidate = self.acceleration_ready if self.acceleration_folder == self.data_folder else None
            if candidate is None:
                return False
            if self.saver is not None and self.saver.is_alive():
                return False
            if self.online_worker is not None and self.online_worker.is_alive():
                return False
            if self.control_stop.is_set() and self.mode == 'control':
                return False
            self.acceleration_ready = None
        previous = self.brain
        if previous is None or self.exit_stop.is_set():
            candidate.close()
            return False
        if io is not None:
            self.backend_recovering.set()
        released = io is None
        try:
            if io is not None:
                io.quick_release()
                released = True
            with previous.save_lock:
                old_rows = list(previous.memory)
                old_steps = previous.steps
                old_generation = previous.generation
            with candidate.save_lock:
                new_count = len(candidate.memory)
                new_steps = candidate.steps
                new_generation = candidate.generation
                new_first = candidate.memory[0] if candidate.memory else None
                new_last = candidate.memory[-1] if candidate.memory else None
            same_rows = new_count == len(old_rows) and (not old_rows or (old_rows[0] == new_first and old_rows[-1] == new_last))
            if not same_rows and (old_steps > new_steps or old_generation >= new_generation):
                difference = old_steps - new_steps
                boundary_matches = difference == len(old_rows) and new_count == 0 or (0 < difference < len(old_rows) and new_last == old_rows[-difference - 1])
                if difference > 0 and boundary_matches:
                    candidate.append_records(old_rows[-difference:], old_steps)
                else:
                    candidate.sync_fast(old_rows, max(old_steps, new_steps))
            self.brain = candidate
            self.brain_folder = self.data_folder
            self.next_backend_retry = 0.
            self.post('backend', candidate.label)
            try:
                previous.close()
            except Exception as error:
                self.post('status', '旧计算资源释放出现问题：' + str(error)[:70])
            if io is not None:
                try:
                    self.start_online()
                except Exception as error:
                    self.post('status', 'GPU 在线训练尚未启动：' + str(error)[:75])
            self.post('status', '已切换到 ' + candidate.label + '，已有交互经验继续保留')
            return True
        except Exception as error:
            candidate.close()
            if io is not None and not released:
                try:
                    io.quick_release()
                except (OSError, RuntimeError):
                    self.post('error', 'GPU 切换时鼠标键释放失败；正在继续尝试，按任意键可停止')
            self.post('accelerator', 'GPU 切换未完成，CPU 学习仍可使用：' + str(error)[:80])
            return False
        finally:
            if io is not None:
                self.backend_recovering.clear()
                self.control_heartbeat = time.monotonic()

    def load(self, task_stop):
        if self.brain is not None and self.brain_folder != self.data_folder:
            self.brain.save()
            self.brain.close()
            self.brain = None
            self.brain_folder = None
        if task_stop.is_set() or self.exit_stop.is_set():
            return
        if self.brain is None:
            self.post('phase', '快速启动学习引擎')
            self.post('status', '正在读取已有经验；GPU 加速将独立在后台准备')
            self.brain = LiteBrain(self.data_folder)
            if self.mode == 'control':
                self.post('progress', (40, '基础学习引擎已加载'))
            self.brain_folder = self.data_folder
            self.post('backend', self.brain.label)
            self.start_capture_preparation()
        if not self.upgrade_backend():
            self.start_acceleration()

    def start_capture_preparation(self):
        if getattr(self, 'capture_worker', None) is not None and self.capture_worker.is_alive():
            return
        folder = self.folder
        self.capture_worker = threading.Thread(target=ensure_capture, args=(folder, lambda msg: None, self.exit_stop), daemon=True)
        self.capture_worker.start()

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
            recovery_cancel = AnyStop(self.exit_stop, self.sleep_stop if self.mode == 'sleep' else self.control_stop)
            self.post('status', '计算后端异常，先尝试恢复 GPU：' + str(error)[:75])
            for backend, runtime in choices:
                if recovery_cancel.is_set():
                    break
                key = (backend, str(runtime) if runtime else '')
                if key in seen:
                    continue
                seen.add(key)
                attempts, previous = failures.get(key, (0, 0.))
                backoff = min(600., math.pow(2., min(attempts, 9)))
                if attempts > 0 and not (key == faulty and attempts == 1) and time.monotonic() - previous < backoff:
                    continue
                candidate = None
                try:
                    candidate = RemoteBrain(self.data_folder, runtime, backend, recovery_cancel)
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
            if isinstance(former, LiteBrain):
                former.close()
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
        if active is not None and (self.release_worker is None or not self.release_worker.is_alive()):
            def release_now():
                try:
                    active.halt()
                    if any(active.down.values()):
                        raise RuntimeError('仍有鼠标键未确认释放')
                except Exception as error:
                    self.post('error', '鼠标释放待重试：' + str(error)[:110])
            self.release_worker = threading.Thread(target=release_now, daemon=True)
            self.release_worker.start()
        if reason:
            self.post('status', reason)

    def online_job(self, brain):
        while not self.online_stop.wait(max(.012, min(.18, float(getattr(brain, 'recent_inference_cost', .04))))) and not self.exit_stop.is_set() and not self.control_stop.is_set():
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
        if not self.keyboard_ready.wait(.3) or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
            self.status.set('键盘监控尚未准备好，不能安全接管鼠标')
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
        self.data_folder, self.environment_code = environment_for(self.folder, hwnd, self.combo_var.get())
        try:
            if not u.IsWindow(hwnd):
                raise RuntimeError('所选窗口已经关闭，请刷新窗口列表')
            u.ShowWindow(hwnd, 9)
            u.SetForegroundWindow(hwnd)
            if int(u.GetForegroundWindow() or 0) != int(hwnd):
                raise RuntimeError('无法激活窗口，检查是否被权限更高的程序阻止')
            rect = RECT()
            point = POINT(0, 0)
            if not u.GetClientRect(hwnd, ctypes.byref(rect)) or not u.ClientToScreen(hwnd, ctypes.byref(point)):
                raise RuntimeError('无法获取目标窗口客户区')
            width, height = rect.right - rect.left, rect.bottom - rect.top
            if width < 80 or height < 60:
                raise RuntimeError('目标窗口客户区太小')
            point_cursor = POINT()
            if not u.GetCursorPos(ctypes.byref(point_cursor)):
                raise RuntimeError('无法读取鼠标位置')
        except Exception as error:
            self.phase.set('无法启动')
            self.issue.set(str(error))
            self.status.set('鼠标无法进入所选窗口：' + str(error))
            return
        self.phase.set('窗口已激活 · 准备模型')
        self.set_progress(0, '启动目标窗口')
        self.issue.set('无')
        self.status.set('正在准备 AI 模型；就绪后自动将光标移入目标窗口客户区')
        self.control_details.set('等待模型就绪 · 鼠标尚未接管')
        self.control_stop.clear()
        self.backend_recovering.clear()
        self.mouse_monitor_armed.clear()
        self.mode = 'control'
        self.worker = threading.Thread(target=self.control_job, args=(hwnd,), daemon=True)
        self.control_worker = self.worker
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
                if active is not None and active.keyboard_activity():
                    self.control_stop.set()
                    self.online_stop.set()
                    self.post('status', '检测到键盘输入，已停止鼠标控制')
                elif not self.keyboard_ready.is_set() or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
                    self.keyboard_ready.clear()
                    self.mouse_monitor_armed.clear()
                    if active is not None:
                        try:
                            active.quick_release()
                        except Exception:
                            pass
                elif not self.backend_recovering.is_set() and self.mouse_monitor_armed.is_set() and self.control_heartbeat > 0 and time.monotonic() - self.control_heartbeat > self.watchdog_limit:
                    self.mouse_monitor_armed.clear()
                    if active is not None:
                        try:
                            active.quick_release()
                        except Exception:
                            pass
                    self.post('status', '计算响应缓慢，已释放鼠标按键；恢复后自动继续')
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

    def keyboard_supervisor(self):
        if os.name != 'nt':
            return
        failures = 0
        while not self.exit_stop.is_set():
            self.keyboard_sentinel()
            if self.exit_stop.is_set():
                break
            failures += 1
            self.post('status', '键盘急停监控正在自动恢复，恢复前禁止鼠标动作')
            self.exit_stop.wait(min(8., math.sqrt(failures)))

    def keyboard_sentinel(self):
        if os.name != 'nt':
            return
        key_hook = None
        mouse_hook = None
        try:
            self.key_thread_id = int(kernel32.GetCurrentThreadId())
            u.PeekMessageW(ctypes.byref(wintypes.MSG()), None, 0, 0, 0)
            def pressed(code, wparam, lparam):
                if code >= 0 and int(wparam) in (0x100, 0x104) and self.mode == 'control' and not self.control_stop.is_set():
                    self.control_stop.set()
                    self.mouse_monitor_armed.clear()
                    self.online_stop.set()
                    self.post('status', '检测到键盘输入，已紧急停止鼠标控制')
                return u.CallNextHookEx(None, code, wparam, lparam)
            def scrolled(code, wparam, lparam):
                if code >= 0 and self.mode == 'control':
                    try:
                        event = ctypes.cast(lparam, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                        kind = int(wparam)
                        injected_by_ai = bool(event.flags & 0x01) and event.extra == AI_INPUT_MARK
                        if kind == 0x20A and injected_by_ai:
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
                self.post('status', '鼠标滚轮监控未启动，仍可正常使用键盘急停与 AI 鼠标控制')
            self.wheel_hook_ready = bool(mouse_hook)
            self.keyboard_alive_at = time.monotonic()
            self.keyboard_ready.set()
            msg = wintypes.MSG()
            while not self.exit_stop.is_set():
                while u.PeekMessageW(ctypes.byref(msg), None, 0, 0, 1):
                    if msg.message == 0x12:
                        raise RuntimeError('键盘监控消息队列已退出')
                self.keyboard_alive_at = time.monotonic()
                self.exit_stop.wait(.012)
        except Exception as ex:
            self.post('status', '键盘安全监控异常：' + str(ex)[:85])
        finally:
            self.keyboard_ready.clear()
            self.keyboard_alive_at = 0.
            self.wheel_hook_ready = False
            self.mouse_monitor_armed.clear()
            if mouse_hook:
                u.UnhookWindowsHookEx(mouse_hook)
            if key_hook:
                u.UnhookWindowsHookEx(key_hook)
            self.key_thread_id = None
            if self.mode == 'control' and not self.exit_stop.is_set():
                self.post('status', '键盘钩子已退出，鼠标控制已暂停；键盘监控恢复前不会继续操作')

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

    def end_experience(self, feedback=None):
        brain = self.brain
        if brain is not None:
            try:
                if isinstance(brain, RemoteBrain):
                    brain.mark_last_done()
                else:
                    with brain.save_lock:
                        if brain.memory and not brain.memory[-1][6]:
                            row = brain.memory.pop()
                            brain.memory.append((*row[:6], True, *row[7:]))
            except Exception as error:
                self.post('status', '交互阶段结束标记待恢复：' + str(error)[:75])
        if feedback is not None:
            feedback.reset_segment()
        self.control_history.clear()

    def schedule_checkpoint(self):
        if self.brain is None or (self.saver is not None and self.saver.is_alive()):
            return
        brain = self.brain
        snapshot_step = self.iterations
        def persist():
            started = time.monotonic()
            try:
                if isinstance(brain, RemoteBrain):
                    brain.checkpoint()
                else:
                    brain.save()
                atlas = self.goal_atlas
                if atlas is not None:
                    atlas.save()
                self.last_checkpoint_step = snapshot_step
                self.last_checkpoint_time = time.monotonic()
                elapsed = self.last_checkpoint_time - started
                self.last_checkpoint_duration = elapsed if not self.last_checkpoint_duration else .75 * self.last_checkpoint_duration + .25 * elapsed
            except Exception as ex:
                self.post('error', '定期保存失败：' + str(ex)[:110])
        self.saver = threading.Thread(target=persist, daemon=True)
        self.saver.start()

    def await_target(self, device, stop, detail):
        self.mouse_monitor_armed.clear()
        self.control_heartbeat = 0.
        try:
            device.quick_release()
        except (OSError, RuntimeError):
            pass
        self.post('phase', '等待目标窗口')
        self.post('status', '暂时暂停，已释放鼠标按键；' + str(detail)[:95] + '。返回目标窗口后自动继续，按任意键停止')
        while not stop.is_set():
            if not self.keyboard_ready.is_set() or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
                stop.wait(.05)
                continue
            region = device.region()
            if region is not None and device.foreground():
                try:
                    device.prepare_cursor(region, stop)
                    self.post('phase', 'AI 控制中')
                    self.post('status', '目标客户区已恢复，AI 继续控制；按任意键停止')
                    self.control_heartbeat = time.monotonic()
                    self.mouse_monitor_armed.set()
                    return region
                except InterruptedError:
                    raise
                except (OSError, RuntimeError, ValueError):
                    pass
            stop.wait(.2)
        raise InterruptedError('键盘已停止鼠标控制')

    def control_job(self, hwnd):
        io = None
        ticks = 0
        last_experience = None
        feedback = Feedback()
        planner = None
        infer_times = deque(maxlen=96)
        capture_times = deque(maxlen=96)
        frame_times = deque(maxlen=96)
        stop = AnyStop(self.control_stop, self.exit_stop)
        try:
            self.load(self.control_stop)
            if not stop.is_set():
                planner = GoalAtlas(self.data_folder)
                self.goal_atlas = planner
                self.post('goal', f'延续 {len(planner.states)} 个历史状态 · 寻找可验证目标')
            if stop.is_set():
                return
            self.post('phase', '检查目标窗口与截图')
            while not stop.is_set() and io is None:
                try:
                    io = WindowsIO(hwnd)
                    io.keyboard_guard = self.keyboard_ready
                except (OSError, RuntimeError, ValueError) as error:
                    self.post('phase', '等待截图设备')
                    self.post('status', '正在恢复鼠标或截图设备：' + str(error)[:90] + '；按任意键停止')
                    stop.wait(.5)
            if stop.is_set():
                return
            self.post('progress', (65, '已启动截图及安全输入'))
            self.active_io = io
            region = self.await_target(io, stop, '正在检查所选窗口的可操作区域')
            self.post('status', '目标窗口与鼠标已验证，正在读取窗口画面')
            while not stop.is_set():
                try:
                    prev_frame = io.image(region)
                    break
                except (OSError, RuntimeError, ValueError) as error:
                    stop.wait(.2)
                    region = self.await_target(io, stop, error)
            if stop.is_set():
                return
            previous_epoch = io.capture_epoch
            invalid_frames = 0
            prev_pos = io.cursor()
            prev_dt = .075
            prev_change = 0.
            last_scroll = 0
            last_tick = time.monotonic()
            self.last_checkpoint_step = self.iterations
            self.last_checkpoint_time = time.monotonic()
            self.control_history.clear()
            holdout_mode = False
            holdout_remaining = max(8, int(math.sqrt(REPLAY_LIMIT)))
            self.audit_sum = 0.
            self.audit_samples = 0
            self.start_online()
            if not self.keyboard_ready.is_set():
                raise RuntimeError('键盘监控未就绪，暂不发送鼠标动作')
            self.control_heartbeat = time.monotonic()
            self.mouse_monitor_armed.set()
            self.post('progress', (100, '鼠标控制已就绪'))
            self.post('phase', 'AI 控制中')
            self.post('status', '正在执行鼠标动作并收集交互经验；任意键立即停止')
            while not stop.is_set():
                try:
                    if self.upgrade_backend(io):
                        self.end_experience(feedback)
                        if stop.is_set():
                            raise InterruptedError('GPU 切换期间收到急停')
                        io.prepare_cursor(region, stop)
                        prev_frame = io.image(region)
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = .075
                        prev_change = 0.
                        self.control_heartbeat = time.monotonic()
                        self.mouse_monitor_armed.set()
                    if not self.keyboard_ready.is_set():
                        raise RuntimeError('键盘监控暂时不可用')
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
                        raise RuntimeError('目标窗口已关闭、最小化或失去焦点，暂停动作')
                    if current_region != region:
                        io.release()
                        self.end_experience(feedback)
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
                        io.quick_release()
                        self.end_experience(feedback)
                        prev_frame = frame
                        prev_change = 0.
                        previous_epoch = frame_epoch
                    if not io.last_frame_valid:
                        invalid_frames += 1
                        if invalid_frames == 1:
                            io.quick_release()
                            self.end_experience(feedback)
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
                    suggested_targets = io.semantic_targets(region)
                    advice = planner.plan(frame, candidates(io.down)) if planner is not None else None
                    try:
                        action, ctrl = self.brain.choose(frame, meta, io.down, suggested_targets)
                    except Exception as ex:
                        self.recover_learning_backend(ex)
                        if stop.is_set():
                            raise InterruptedError('后端恢复期间收到急停')
                        io.prepare_cursor(region, stop)
                        self.control_heartbeat = time.monotonic()
                        self.mouse_monitor_armed.set()
                        action, ctrl = self.brain.choose(frame, meta, io.down, suggested_targets)
                    if advice is not None and random.random() < advice[1] and advice[2] > 0.:
                        if action != advice[0]:
                            action = advice[0]
                            ctrl = anchor_control(action)
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
                    if feedback.stagnant > math.sqrt(max(1, feedback.total)) and feedback.loop_count > math.sqrt(max(1, feedback.progress_effects + 1)):
                        safer = [item for item in candidates(io.down) if not ACT[item][3].endswith('+') and not ACT[item][4]]
                        action = explore_action(safer, meta, self.brain.steps, frame, io.semantic_targets(region))
                        ctrl = exploratory_control(action, meta)
                    if len(ctrl) != CTRL_N or not all(math.isfinite(v) for v in ctrl):
                        raise RuntimeError('模型动作参数异常')
                    io.safe(region, stop)
                    median_cycle = sorted(frame_times)[len(frame_times) // 2] if frame_times else max(.015, capture_ms / 1000. + infer_ms / 1000.)
                    duration = max(.015, min(.25, ctrl[7] * max(median_cycle, capture_ms / 1000. + infer_ms / 1000.)))
                    execution_start = time.monotonic()
                    outcome = io.act(normalize_control(ctrl), region, stop, duration)
                    action_finished = time.monotonic()
                    outcome['requested_action'] = action
                    outcome['intended_ctrl'] = normalize_control(ctrl)
                    if self.control_stop.wait(max(0., duration - (time.monotonic() - execution_start))) or stop.is_set():
                        break
                    if io.region() != region:
                        io.quick_release()
                        self.end_experience(feedback)
                        updated = io.region()
                        if updated is None or not io.foreground():
                            raise RuntimeError('窗口区域暂时不可用，暂停动作')
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
                    nxt = io.fresh_image(region, action_finished, frame_epoch, stop)
                    capture_times.append(capture_ms + io.last_capture_ms)
                    if nxt is None or io.capture_epoch != frame_epoch or not io.last_frame_valid:
                        io.quick_release()
                        self.end_experience(feedback)
                        previous_epoch = io.capture_epoch
                        prev_frame = io.image(region)
                        prev_pos = io.cursor()
                        prev_dt = dt
                        prev_change = 0.
                        self.post('status', '动作后的新帧未到达或捕获源发生切换，已丢弃本次训练样本')
                        continue
                    frame_times.append(tick_interval)
                    new_mouse = io.cursor()
                    reward, change, advanced = feedback.assess(frame, nxt, prev_frame, outcome, new_mouse, region)
                    if planner is not None:
                        planner.observe(frame, action, nxt, reward, outcome['efficacy'], advanced)
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
                    self.post('control', f'方向 ({executed[0]:+.2f}, {executed[1]:+.2f}) · 移动 {outcome["moved"] / max(.001, duration):.0f} px/s · 左键 {"按下" if buttons["l"] else "释放"} · 右键 {"按下" if buttons["r"] else "释放"} · 中键 {"按下" if buttons["m"] else "释放"} · 滚轮 {wheel_speed:+.0f}/s')
                    if ticks % 32 == 0:
                        def p95(samples):
                            ordered = sorted(samples)
                            return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * .95))] if ordered else 0.
                        fps = len(frame_times) / max(.001, sum(frame_times))
                        perf = self.brain.latest_perf if isinstance(self.brain, RemoteBrain) else {}
                        gpu_training = f' · 训练 {perf["training_samples_per_second"]:.1f}样本/s · 批量 {perf["batch_size"]} · 传输 {perf["transfer_ms"]:.1f}ms' if perf and self.brain.accelerated else ''
                        if perf and 'gpu_memory_total_gb' in perf:
                            gpu_training += f' · 显存 {perf["gpu_memory_used_gb"]:.2f}/{perf["gpu_memory_total_gb"]:.2f}GB'
                        if perf and 'capacity_layers' in perf:
                            gpu_training += f' · 思维层 {perf["capacity_layers"]} · 视觉层 {perf.get("vision_layers", 0)} · 参数 {perf["model_parameters"]:,} · 世界模型 {perf.get("world_models", 2)} 个'
                            if 'visual_error' in perf:
                                gpu_training += f' · 视觉重建误差 {perf["visual_error"]:.4f}'
                            if perf.get('world_model_ratio') is not None:
                                gpu_training += f' · 预见可信度 {100 * perf["planning_trust"]:.0f}%'
                        prediction = feedback.prediction_error / max(1, feedback.total)
                        causal = feedback.causal_total / max(1, feedback.total)
                        capture_status = f' · 截图 {io.last_frame_backend or "未定"} {io.last_capture_ms:.0f}ms'
                        failures = sum(io.capture_failures.values())
                        if failures:
                            capture_status += f' · 捕获回退 {failures} 次'
                        self.post('capture', f'{io.last_frame_backend or "未定"} · 采集 {io.last_capture_ms:.0f}ms · {fps:.1f}FPS · 推理 P95 {p95(infer_times):.0f}ms' + (f' · 自动回退 {failures} 次' if failures else ''))
                        archive = getattr(self.brain, 'archive', None)
                        archived = archive.kept if archive is not None else perf.get('archive_count', '后台保存')
                        self.post('goal', planner.description if planner is not None else '目标规划未启动')
                        self.post('stats', f'短期经验 {len(self.brain.memory)} · 长期经验 {archived} · 操作 {self.iterations} · 可控进展 {feedback.progress_effects}/{feedback.total} · 循环 {feedback.loop_count} · 预测误差 {prediction:.3f} · 因果关联 {causal:.2f} · 受阻 {feedback.blocks}（均非任务成功率）' + gpu_training)
                    with self.brain.save_lock:
                        saved_count = len(self.brain.memory)
                    pending = self.iterations - self.last_checkpoint_step
                    minimum_samples = max(8, int(math.sqrt(max(1, saved_count))))
                    minimum_seconds = max(5., self.last_checkpoint_duration * 12., math.log2(2. + saved_count))
                    if pending >= minimum_samples and time.monotonic() - self.last_checkpoint_time >= minimum_seconds:
                        self.schedule_checkpoint()
                    prev_frame = nxt
                    prev_pos = new_mouse
                    prev_change = change
                    prev_dt = actual_dt
                    last_scroll = outcome['scroll']
                except InterruptedError:
                    raise
                except (OSError, RuntimeError, ValueError, TimeoutError) as failure:
                    if stop.is_set():
                        raise InterruptedError('键盘已停止鼠标控制')
                    io.quick_release()
                    self.end_experience(feedback)
                    stop.wait(.2)
                    region = self.await_target(io, stop, failure)
                    prev_frame = io.image(region)
                    previous_epoch = io.capture_epoch
                    invalid_frames = 0
                    prev_pos = io.cursor()
                    prev_dt = .075
                    prev_change = 0.
                    last_tick = time.monotonic()
            if self.control_stop.is_set():
                self.post('status', '鼠标控制已停止；可以再次开始或让 AI 睡眠学习')
        except InterruptedError:
            self.post('status', '紧急停止已执行')
        except RuntimeError as ex:
            self.post('error', '控制发生无法自动恢复的问题：' + str(ex)[:125])
        except Exception as ex:
            self.post('error', '控制发生无法自动恢复的问题：' + str(ex)[:125])
        finally:
            self.mouse_monitor_armed.clear()
            self.control_heartbeat = 0.
            self.online_stop.set()
            if io is not None:
                try:
                    io.halt()
                except Exception:
                    pass
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
                finally:
                    self.active_io = None
            if self.brain is not None:
                try:
                    if last_experience is not None:
                        self.end_experience(feedback)
                    if self.saver is not None and self.saver.is_alive():
                        self.saver.join(timeout=max(8., self.watchdog_limit * 3.))
                        if self.saver.is_alive():
                            raise TimeoutError('后台保存未结束，已避免同时写入模型；由原保存任务继续完成')
                    self.brain.save()
                    if planner is not None:
                        planner.save()
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
            if self.goal_atlas is planner:
                self.goal_atlas = None
            self.post('done', 'control')

    def sleep(self):
        if self.mode == 'sleep':
            self.status.set('AI 正在睡眠训练中')
            return
        if self.mode == 'control':
            self.status.set('控制期间仅按下键盘按键才能停止；停止后再点击黑色按钮睡眠')
            return
        if self.mode != 'idle' or self.switching_folder:
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is not None and os.name == 'nt' and not u.IsWindow(hwnd):
            self.status.set('目标窗口已关闭，请刷新窗口列表')
            return
        if hwnd is not None:
            environment = environment_for(self.folder, hwnd, self.combo_var.get())
        elif self.brain is not None and self.brain_folder == self.data_folder:
            environment = (self.data_folder, self.environment_code)
        else:
            self.status.set('请先选择有学习经验的目标窗口')
            return
        previous = self.worker if self.worker is not None and self.worker.is_alive() else None
        self.sleep_stop.clear()
        self.mode = 'sleep'
        self.phase.set('睡眠训练')
        self.set_progress(0, '睡眠准备')
        self.issue.set('无')
        self.status.set('正在停止鼠标控制，随后验证并巩固交互经验')
        self.worker = threading.Thread(target=self.sleep_job, args=(previous, environment), daemon=True)
        self.worker.start()

    def sleep_job(self, previous, environment):
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
            if self.exit_stop.is_set() or self.sleep_stop.is_set():
                return
            self.data_folder, self.environment_code = environment
            if self.brain is not None and self.brain_folder == self.data_folder:
                has_experience = bool(self.brain.memory)
            else:
                latest = newest_replay(self.data_folder)
                has_experience = latest is not None and bool(latest[2])
            if not has_experience:
                self.post('status', '尚无交互经验；先点击绿色按钮让 AI 感知并探索窗口')
                self.post('progress', (100, '检查完成 · 尚无训练经验'))
                return
            self.load(self.sleep_stop)
            self.post('progress', (12, '学习经验加载完成'))
            if self.sleep_stop.is_set() or self.exit_stop.is_set():
                return
            mem = len(self.brain.memory)
            if not mem:
                self.post('status', '没有可训练的交互经验，本次不启动睡眠训练')
                self.post('progress', (100, '经验检查完成 · 无训练数据'))
                return
            self.post('status', f'AI 睡眠中：使用近期 {mem} 条经验与长期精选经验进行验证式巩固…')
            if hasattr(self.brain, 'begin_sleep'):
                self.brain.begin_sleep()
            capacity = getattr(self.brain, 'latest_capacity', None)
            if isinstance(capacity, dict):
                self.post('status', f'正在验证式学习 · 思维扩展层 {capacity["capacity_layers"]} · 视觉扩展层 {capacity.get("vision_layers", 0)} · 世界模型 {capacity.get("world_models", 2)} 个 · 参数 {capacity["parameters"]:,}' + (' · 本轮新增学习容量' if capacity['expanded'] else ''))
            steps = 0
            validation = sleep_split(list(self.brain.memory))
            if validation is None:
                if hasattr(self.brain, 'end_sleep'):
                    self.brain.end_sleep()
                self.post('status', '尚未收集足够的独立验证和审计经验，本次不训练，避免把训练损失误判成真实提升')
                self.post('progress', (100, '验证检查完成 · 数据不足'))
                return
            base_budget = mem * max(2, int(math.log2(1. + mem)))
            ceiling = base_budget
            check_span = max(8, int(math.sqrt(mem)))
            self.post('progress', (20, '预留验证集已建立'))
            best_loss = None
            changes = deque(maxlen=max(3, int(math.log2(1. + mem))))
            next_check = check_span
            while steps < ceiling and not self.sleep_stop.is_set() and not self.exit_stop.is_set():
                chunk = min(check_span, ceiling - steps)
                try:
                    n = self.brain.train(chunk, self.sleep_stop)
                except Exception as ex:
                    self.recover_learning_backend(ex)
                    self.post('status', '训练后端发生变化，已取消本轮睡眠以避免未经验证的模型更新')
                    return
                steps += n
                self.post('progress', (20. + 75. * (1. - math.exp(-steps / max(1, base_budget))), f'验证式睡眠训练 {steps} 批'))
                if n == 0:
                    break
                if steps >= next_check and hasattr(self.brain, 'sleep_progress'):
                    self.post('stats', f'经验 {mem} 条 · 睡眠更新 {steps}/{ceiling} 批 · 实际改进以预留验证为准')
                    next_check = steps + check_span
                    loss = self.brain.sleep_progress()
                    if loss is not None and math.isfinite(loss):
                        tolerance = (abs(best_loss) + 1e-8) / math.sqrt(max(2, len(validation[1]))) if best_loss is not None else 0.
                        improvement = max(0., best_loss - loss - tolerance) if best_loss is not None else 0.
                        changes.append(improvement)
                        if best_loss is None or loss < best_loss:
                            best_loss = loss
                        if len(changes) == changes.maxlen and sum(changes) <= (abs(best_loss) + 1e-8) / math.sqrt(mem):
                            break
                        if steps + check_span >= ceiling and sum(changes) > max(1e-8, abs(best_loss) / math.sqrt(max(2, len(validation[1])))):
                            ceiling += max(check_span, int(base_budget / math.sqrt(1. + steps / max(1, base_budget))))
            result = self.brain.end_sleep() if hasattr(self.brain, 'end_sleep') else None
            self.brain.save()
            if not self.sleep_stop.is_set() and not self.exit_stop.is_set():
                self.post('progress', (100, '睡眠训练验证及保存完成'))
            else:
                self.post('progress', (min(99., 20. + 75. * (1. - math.exp(-steps / max(1, base_budget)))), '训练已中断，结果已安全处理'))
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
            self.post('progress', (100, '睡眠任务已结束 · 发生异常'))
        finally:
            if self.sleep_stop.is_set() and not self.exit_stop.is_set():
                self.post('progress', (100, '已唤醒 · 本轮训练结束'))
            self.post('done', 'sleep')

    def wake(self):
        if self.mode == 'sleep':
            self.sleep_stop.set()
            if isinstance(self.brain, RemoteBrain):
                self.brain.cancel_train()
            self.status.set('正在取消后续训练批次并保存经验…')
            self.progress_text.set('正在唤醒 · ' + f'{self.progress_value.get():.0f}%')
        else:
            self.status.set('AI 当前没有睡觉')

    def close(self):
        if self.mode == 'closed':
            return
        self.mode = 'closed'
        self.update_buttons()
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
        self.acceleration_cleanup = threading.Thread(target=self.cleanup_background, daemon=True)
        self.acceleration_cleanup.start()
        self.phase.set('正在退出')
        self.status.set('正在释放鼠标并保存学习数据…')
        if os.name == 'nt' and self.key_thread_id is not None:
            try:
                u.PostThreadMessageW(self.key_thread_id, 0x12, 0, 0)
            except Exception:
                pass
        self.exit_backup = threading.Thread(target=self.emergency_snapshot, daemon=True)
        self.exit_backup.start()
        self.set_progress(0, '正在安全退出')
        self.root.after(40, self.finish_close)

    def cleanup_background(self):
        try:
            try:
                self.cancel_acceleration()
            finally:
                stop_all_processes()
            for task in (self.acceleration_thread, self.capture_worker):
                if task is not None and task.is_alive() and task is not threading.current_thread():
                    task.join()
        except Exception as error:
            self.post('error', '关闭安装组件时出现异常：' + str(error)[:115])
        finally:
            stop_all_processes()

    def emergency_snapshot(self):
        brain = self.brain
        if brain is None:
            return
        try:
            with brain.save_lock:
                records = list(brain.memory)
                generation = max(brain.generation, getattr(brain, 'latest_replay_generation', 0), getattr(brain, 'model_generation', 0)) + 1
            if records:
                if not records[-1][6]:
                    row = records[-1]
                    records[-1] = (*row[:6], True, *row[7:])
                brain.folder.mkdir(parents=True, exist_ok=True)
                save_replay(brain.folder, records, 'recovery', generation)
        except Exception as error:
            self.exit_backup_error = str(error)[:150]

    def finish_close(self):
        elapsed = time.monotonic() - self.close_started
        deadline = min(30., max(12., self.watchdog_limit * 4.))
        busy = any(task is not None and task.is_alive() for task in (self.worker, self.control_worker, self.saver, self.online_worker, self.acceleration_cleanup, self.acceleration_thread, self.capture_worker, self.key_thread, self.safety_thread, self.exit_backup, self.release_worker))
        main_busy = any(task is not None and task.is_alive() for task in (self.worker, self.saver, self.online_worker))
        if self.shutdown_worker is None and (not main_busy or elapsed > deadline * .7):
            def cleanup():
                if self.brain is not None:
                    try:
                        self.brain.close()
                    except Exception:
                        pass
            self.shutdown_worker = threading.Thread(target=cleanup, daemon=True)
            self.shutdown_worker.start()
        busy |= self.shutdown_worker is not None and self.shutdown_worker.is_alive()
        self.set_progress(100. * min(1., elapsed / deadline), '正在释放资源并保存恢复点')
        if busy and elapsed < deadline:
            self.root.after(100, self.finish_close)
            return
        if busy:
            self.status.set('已达到退出等待上限，强制结束仍未响应的后台任务；恢复数据优先从最新检查点加载')
            threading.Thread(target=stop_all_processes, daemon=True).start()
        elif self.exit_backup_error is not None:
            self.status.set('紧急备份未完成：' + self.exit_backup_error)
        self.set_progress(100, '退出完成')
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
