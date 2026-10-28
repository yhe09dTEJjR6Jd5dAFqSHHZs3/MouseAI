import os
import sys
import sysconfig
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
import urllib.error
import urllib.parse
import html
import multiprocessing as mp
from multiprocessing import shared_memory
import atexit
import sqlite3
import zlib
import heapq
from pathlib import Path
from collections import deque, Counter
from functools import lru_cache
import tkinter as tk
from tkinter import ttk, filedialog

VIS_W = 512
VIS_H = 288
ENC_H = max(8, VIS_H // 24)
ENC_W = max(12, VIS_W // 26)
RECON_H = max(12, VIS_H // 12)
RECON_W = max(20, VIS_W // 12)
CELL_H = max(1, VIS_H // 18)
CELL_W = max(1, VIS_W // 16)
CELLS_PER_VIEW = (VIS_H // CELL_H) * (VIS_W // CELL_W)
PIXELS = VIS_W * VIS_H
CHANNELS = 3
VIS_N = PIXELS * CHANNELS * 2
SHARED_FRAME_TOKEN = 'mouseai-shared-frames-v1'
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
REPLAY_MAGIC = b'MOUSEA10'
REPLAY_LEGACY_MAGIC = b'MOUSEAI9'
REPLAY_PACK = struct.Struct('<BBf?ff?' + 'f' * (META_N * 2 + CTRL_N * 2))
DEMONSTRATION_FLAG = 0x80

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


def memory_pressure():
    free = available_memory()
    if free <= 0:
        return 0.
    parallel_copies = max(4, 2 * min(4, os.cpu_count() or 1))
    estimated_budget = VIS_N * 2 * max(1, REPLAY_LIMIT) * parallel_copies
    return max(0., min(1., 1. - free / max(1, estimated_budget)))


def replay_capacity():
    sample_size = (sys.getsizeof(bytes(VIS_N)) * 2 +
                   sys.getsizeof(tuple(range(13))) + REPLAY_PACK.size +
                   sys.getsizeof(tuple(range(META_N))) * 2 +
                   sys.getsizeof(tuple(range(CTRL_N))) * 2)
    free = available_memory()
    copies = max(4, 2 * min(4, os.cpu_count() or 1))
    available = max(1, int(free // max(1, sample_size * copies))) if free else max(1, os.cpu_count() or 1)
    try:
        inherited = int(os.environ.get('MOUSEAI_REPLAY_CAPACITY', '0'))
        return min(available, inherited) if inherited > 0 and not os.environ.get('MOUSEAI_REPLAY_LOCKED') else (inherited if inherited > 0 else available)
    except (TypeError, ValueError, OverflowError):
        return available

REPLAY_LIMIT = replay_capacity()
os.environ['MOUSEAI_REPLAY_CAPACITY'] = str(REPLAY_LIMIT)
os.environ['MOUSEAI_REPLAY_LOCKED'] = '1'
ACT = [(0, 0, 0, '', 0)]
for x, y in ((1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)):
    norm = math.hypot(x, y)
    ACT.append((x / norm, y / norm, 1., '', 0))
ACT += [(0, 0, 0, name + state, 0) for name in 'lrm' for state in '+-']
ACT += [(0, 0, 0, '', sign) for sign in (1., -1.)]
ACT_N = len(ACT)
MOTION_ACTIONS = tuple(i for i, a in enumerate(ACT) if a[2] > 0.)
SCROLL_ACTIONS = tuple(i for i, a in enumerate(ACT) if a[4])
BUTTON_ACTIONS = {(a[3][0], a[3][-1] == '+'): i for i, a in enumerate(ACT) if a[3]}
IDLE_ACTION = next(i for i, a in enumerate(ACT) if not (a[2] or a[3] or a[4]))


atexit.register(stop_all_processes)

def speed_reference(region, dt):
    _, _, w, h = region
    return math.hypot(w, h)

def adaptive_exploration(steps, updates, uncertainty=1.):
    observations = max(0., float(updates))
    if not observations:
        return max(0., min(1., float(uncertainty)))
    decisions = max(1., float(steps))
    bound = math.sqrt(math.log(2. * ACT_N * decisions) / (2. * observations))
    return max(0., min(1., float(uncertainty) * bound))

class InputLeaseStop:
    def __init__(self, device):
        self.device = device

    def is_set(self):
        device = self.device
        return bool((device.input_generation_guard is not None and
                     not device.input_generation_guard(device.input_generation)) or
                    (device.keyboard_guard is not None and not device.keyboard_guard.is_set()) or
                    (device.human_guard is not None and not device.human_guard()))


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
    allowed = []
    for i, (_, _, _, button, _) in enumerate(ACT):
        if not button or bool(held.get(button[0], False)) != (button[-1] == '+'):
            allowed.append(i)
    return allowed


def observed_action(dx, dy, dt, speed_limit, wheel=0., delta=0, switches=()):
    if switches:
        return next(index for index, prototype in enumerate(ACT) if prototype[3] == switches[0])
    if delta:
        return min((i for i, prototype in enumerate(ACT) if prototype[4] * delta > 0.),
                   key=lambda i: abs(ACT[i][4] - math.copysign(abs(wheel), delta)))
    if dx or dy:
        distance = math.hypot(dx, dy)
        speed = min(1., distance / (max(sys.float_info.min, dt) * speed_limit))
        vx, vy = dx * speed / distance, dy * speed / distance
        return min((i for i, prototype in enumerate(ACT) if prototype[2] > 0.),
                   key=lambda i: (ACT[i][0] * ACT[i][2] - vx) ** 2 + (ACT[i][1] * ACT[i][2] - vy) ** 2)
    return 0



def demonstration_from_events(old_cursor, cursor, old_held, held, events, region, elapsed):
    x, y, w, h = region
    ordered = sorted((event for event in events if x <= event[3] < x + w and y <= event[4] < y + h), key=lambda event: (event[1], event[0]))
    if not ordered:
        return ()
    cursor_at = tuple(old_cursor)
    pressed = {name: bool(old_held.get(name, False)) for name in ('l', 'r', 'm')}
    samples = []
    previous_time = max(0., ordered[-1][1] - max(sys.float_info.epsilon, elapsed))
    stop_time = max(previous_time, ordered[-1][1])

    def record(action, position, stamp, distance=0., wheel=0, switch=''):
        nonlocal previous_time
        dt = max(sys.float_info.epsilon, stamp - previous_time)
        control = list(anchor_control(action))
        if action in MOTION_ACTIONS and distance > 0.:
            dx, dy = position[0] - cursor_at[0], position[1] - cursor_at[1]
            control[0], control[1] = dx / distance, dy / distance
            control[2] = min(1., distance / (dt * speed_reference(region, dt)))
        samples.append((action, normalize_control(control), distance, (switch,) if switch else (), int(wheel), dt, position, pressed.copy()))
        previous_time = stamp

    motion_total = sum(not event[2] and not event[5] for event in ordered)
    motion_stride = max(1, math.isqrt(max(1, motion_total)))
    motion_seen = 0
    for event in ordered:
        _, stamp, switch, px, py, delta = event
        if not switch and not delta:
            motion_seen += 1
            if motion_seen % motion_stride and motion_seen != motion_total:
                continue
        stamp = max(previous_time, min(float(stamp), stop_time))
        position = (int(px), int(py))
        dx, dy = position[0] - cursor_at[0], position[1] - cursor_at[1]
        distance = math.hypot(dx, dy)
        if distance:
            action = observed_action(dx, dy, max(sys.float_info.epsilon, stamp - previous_time), speed_reference(region, elapsed))
            record(action, position, stamp, distance=distance)
        cursor_at = position
        if switch in ('l+', 'l-', 'r+', 'r-', 'm+', 'm-'):
            name, down = switch[0], switch[1] == '+'
            if pressed[name] != down:
                pressed[name] = down
                record(BUTTON_ACTIONS[(name, down)], position, stamp, switch=switch)
        if delta:
            action = observed_action(0., 0., max(sys.float_info.epsilon, elapsed), speed_reference(region, elapsed), math.copysign(1., delta), delta)
            record(action, position, stamp, wheel=delta)
    final_dx, final_dy = cursor[0] - cursor_at[0], cursor[1] - cursor_at[1]
    if (final_dx or final_dy) and x <= cursor[0] < x + w and y <= cursor[1] < y + h:
        distance = math.hypot(final_dx, final_dy)
        stamp = previous_time + max(sys.float_info.epsilon, elapsed / max(1, len(ordered)))
        action = observed_action(final_dx, final_dy, stamp - previous_time, speed_reference(region, elapsed))
        record(action, tuple(cursor), stamp, distance=distance)
    return tuple(samples)


def permitted_autonomous_control(action, ctrl, demonstrations, held, exploration=()):
    allowed = set(demonstrations)
    allowed.update(exploration)
    for button in ('l', 'r', 'm'):
        if held.get(button, False):
            allowed.add(BUTTON_ACTIONS[(button, False)])
    if action not in MOTION_ACTIONS and action != IDLE_ACTION and action not in allowed:
        action, ctrl = IDLE_ACTION, anchor_control(IDLE_ACTION)
    values = list(normalize_control(ctrl))
    primitive = ACT[action]
    if primitive[3]:
        values[:3] = [0., 0., 0.]
        values[6] = 0.
        for button, channel in (('l', 3), ('r', 4), ('m', 5)):
            values[channel] = (1. if primitive[3][1] == '+' else -1.) if primitive[3][0] == button else 0.
    else:
        values[3:6] = [0., 0., 0.]
        if primitive[4]:
            values[:3] = [0., 0., 0.]
            values[6] = math.copysign(abs(values[6]) if abs(values[6]) > sys.float_info.epsilon else abs(primitive[4]), primitive[4])
        else:
            values[6] = 0.
            if action == IDLE_ACTION:
                values[:3] = [0., 0., 0.]
    return action, normalize_control(values)


class ExplorationEvidence:
    def __init__(self):
        self.tried = set()
        self.tried_order = deque()
        self.last_scene = None
        self.attempts = 0
        self.effects = 0
        self.pending_release = False

    def allowable(self, frame, meta, controls, held):
        if held.get('l', False):
            return {BUTTON_ACTIONS[('l', False)]}
        scene = session_signature(frame)
        point = (round(float(meta[4]) * VIS_W / CELL_W), round(float(meta[5]) * VIS_H / CELL_H))
        allowed = set(controls)
        if (scene, point) in self.tried:
            allowed.discard(BUTTON_ACTIONS[('l', True)])
        self.last_scene = (scene, point)
        return allowed

    def choose(self, action, ctrl, allowed, feedback):
        press = BUTTON_ACTIONS[('l', True)]
        if press not in allowed:
            return action, ctrl
        seen = max(1, feedback.total)
        threshold = max(1, math.isqrt(seen))
        if feedback.stagnant >= threshold and action in MOTION_ACTIONS:
            return press, anchor_control(press)
        return action, ctrl

    def observe(self, action, before, after, outcome):
        if action != BUTTON_ACTIONS[('l', True)] or self.last_scene is None:
            return
        if self.last_scene not in self.tried:
            self.tried.add(self.last_scene)
            self.tried_order.append(self.last_scene)
        while len(self.tried_order) > REPLAY_LIMIT:
            self.tried.discard(self.tried_order.popleft())
        self.attempts += 1
        if (session_signature(before) != session_signature(after) and
                outcome.get('efficacy', 0.) > 0. and not outcome.get('blocked')):
            self.effects += 1


def coalesce_observation(memory, observation):
    if memory:
        previous = memory[-1][3]
        if previous is observation or previous == observation:
            return previous
    return observation


def demonstrated_controls(records):
    index = {}
    for row in records:
        if len(row) < 14 or not row[13] or row[12] or row[11] <= 0.:
            continue
        action = row[2]
        if action in MOTION_ACTIONS or action == IDLE_ACTION:
            continue
        meta = row[1]
        if len(meta) != META_N:
            continue
        try:
            key = (session_signature(row[0]), round(meta[4] * VIS_W / CELL_W), round(meta[5] * VIS_H / CELL_H))
            index.setdefault(key, set()).add(action)
        except (ValueError, TypeError, OverflowError):
            continue
    return index


def matching_demonstrations(index, frame, meta):
    if not index:
        return set()
    signature = session_signature(frame)
    cell_x = round(meta[4] * VIS_W / CELL_W)
    cell_y = round(meta[5] * VIS_H / CELL_H)
    result = set()
    for x in (cell_x - 1, cell_x, cell_x + 1):
        for y in (cell_y - 1, cell_y, cell_y + 1):
            result.update(index.get((signature, x, y), ()))
    return result


def demonstrated_target_cells(index):
    targets = {}
    for (signature, cx, cy), actions in index.items():
        if any(ACT[action][3].endswith('+') for action in actions):
            targets.setdefault(signature, set()).add((cx, cy))
    return targets


def demonstrated_pointer_gain(targets, frame, before, after, region):
    if not targets or before == after:
        return 0.
    x, y, w, h = region
    if w <= 0 or h <= 0:
        return 0.
    signature = session_signature(frame)
    columns = VIS_W / CELL_W
    rows = VIS_H / CELL_H
    start = ((before[0] - x) / w, (before[1] - y) / h)
    finish = ((after[0] - x) / w, (after[1] - y) / h)
    progress = 0.
    for cx, cy in targets.get(signature, ()):
        target = (max(0., min(1., cx / columns)), max(0., min(1., cy / rows)))
        old_dist = math.dist(start, target)
        new_dist = math.dist(finish, target)
        radius = math.hypot(1. / columns, 1. / rows)
        if old_dist > radius and new_dist < old_dist:
            progress = max(progress, min(1., (old_dist - new_dist) / old_dist))
    return progress


def pointer_offset(dx, dy, meta):
    proportion = max(0., min(1., float(meta[15])))
    return dx * proportion, dy * (1. - proportion)


def pointer_pixel_radius(meta):
    proportion = max(0., min(1., float(meta[15])))
    return math.hypot(proportion / VIS_W, (1. - proportion) / VIS_H)


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
    weights = [value / (1. + math.hypot(*pointer_offset(x - mx, y - my, meta))) for x, y, value in salient]
    selected = random.choices(salient, weights=weights, k=1)[0]
    nearest = min(salient, key=lambda item: math.hypot(*pointer_offset(item[0] - mx, item[1] - my, meta)))
    mean_strength = total / len(salient)
    local = nearest[2] / max(1., mean_strength)
    dx, dy = selected[0] - mx, selected[1] - my
    return dx, dy, min(1., local / (1. + local)), min(1., math.hypot(dx, dy))


def careful_choice(values, allowed, steps):
    if not allowed:
        return IDLE_ACTION
    return max(allowed, key=lambda action: (values[action], -action))


def explore_action(allowed, meta=None, steps=0, observation=None, targets=None):
    if not allowed:
        return IDLE_ACTION
    if meta is None:
        return random.choice(allowed)
    mx, my = float(meta[4]), float(meta[5])
    pixel = max(sys.float_info.epsilon, pointer_pixel_radius(meta))
    points = []
    for x, y, quality in targets or ():
        dx, dy = pointer_offset(float(x) - mx, float(y) - my, meta)
        distance = math.hypot(dx, dy)
        points.append((distance, dx, dy, max(0., float(quality))))
    focus = visual_attention(observation, meta)
    if focus is not None:
        dx, dy = pointer_offset(focus[0], focus[1], meta)
        points.append((math.hypot(dx, dy), dx, dy, max(0., focus[2])))
    if not points:
        return random.choice(allowed)
    weights = [quality / (pixel + distance) for distance, _, _, quality in points]
    if not any(weights):
        return random.choice(allowed)
    distance, dx, dy, quality = random.choices(points, weights=weights, k=1)[0]
    scores = []
    for action in allowed:
        vx, vy, speed, button, wheel = ACT[action]
        if speed:
            aspect = max(0., min(1., float(meta[15])))
            step_x, step_y = vx * aspect / VIS_W, vy * (1. - aspect) / VIS_H
            step_size = math.hypot(step_x, step_y)
            gain = (distance - math.hypot(dx - step_x, dy - step_y)) / max(sys.float_info.epsilon, step_size)
        elif button == 'l+' and quality > 0.:
            gain = 1. - distance / pixel
        elif button.endswith('-'):
            gain = 0.
        else:
            gain = -1. if distance > pixel else 0.
        scores.append(math.exp(max(-math.log(sys.float_info.max) / 4., min(1., gain))))
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
    control = [float(ax), float(ay), float(speed), 0., 0., 0., float(wheel), 1.]
    if button:
        control[{'l': 3, 'r': 4, 'm': 5}[button[0]]] = 1. if button[1] == '+' else -1.
    if prediction is not None:
        trust = max(0., min(1., float(trust)))
        prediction = normalize_control(prediction)
        control = [(1. - trust) * old + trust * new for old, new in zip(control, prediction)]
    return normalize_control(control)


def exploratory_control(action, meta=None):
    ctrl = list(anchor_control(action))
    if action in MOTION_ACTIONS:
        directions = sorted({math.atan2(value[1], value[0]) % math.tau for value in ACT if value[2] > 0.})
        span = math.tau / max(1, len(directions))
        angle = math.atan2(ctrl[1], ctrl[0]) + random.uniform(-span / 2., span / 2.)
        ctrl[0], ctrl[1] = math.cos(angle), math.sin(angle)
        ctrl[2] = random.random()
    elif action in SCROLL_ACTIONS:
        ctrl[6] = math.copysign(random.random(), ctrl[6])
    ctrl[7] = 1.
    return normalize_control(ctrl)


class ControlEvidence:
    def __init__(self, records=()):
        self.samples = [deque(maxlen=max(1, REPLAY_LIMIT // ACT_N)) for _ in ACT]
        for row in records:
            self.observe(row)

    def observe(self, row):
        if len(row) < 13 or row[12] or not (0 <= row[2] < ACT_N):
            return
        efficacy = float(row[11])
        if not math.isfinite(efficacy) or efficacy <= 0.:
            return
        control = row[8]
        if len(control) != CTRL_N or not all(math.isfinite(float(v)) for v in control):
            return
        self.samples[row[2]].append((tuple(control), efficacy, float(row[5])))

    def explore(self, action, meta=None):
        control = list(exploratory_control(action, meta))
        observations = self.samples[action]
        if not observations:
            return tuple(control)
        evidence_probability = len(observations) / (len(observations) + 1.)
        if random.random() >= evidence_probability:
            return tuple(control)
        rewards = [max(0., reward) * efficacy for _, efficacy, reward in observations]
        weights = rewards if sum(rewards) > 0. else [efficacy for _, efficacy, _ in observations]
        measured = random.choices(observations, weights=weights, k=1)[0][0]
        if action in MOTION_ACTIONS:
            confidence = len(observations) / (len(observations) + math.sqrt(max(1, self.samples[action].maxlen)))
            control[0] = control[0] * (1. - confidence) + measured[0] * confidence
            control[1] = control[1] * (1. - confidence) + measured[1] * confidence
            control[2] = measured[2]
        if action in SCROLL_ACTIONS:
            control[6] = measured[6]
        control[7] = measured[7]
        return normalize_control(control)


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
    def transition_signature(row):
        return hashlib.blake2s(row[0] + bytes((row[2],)) + row[3], digest_size=12).digest()
    held_out_signatures = {transition_signature(records[i]) for i in held_out}
    train_indices = [i for i, row in enumerate(records) if not excluded[i] and not row[12] and transition_signature(row) not in held_out_signatures]
    training = []
    for offset, index in enumerate(train_indices):
        row = records[index]
        contiguous = offset + 1 < len(train_indices) and train_indices[offset + 1] == index + 1
        training.append(row if contiguous or row[6] else (*row[:6], True, *row[7:]))
    audit_runs = max(1, round(math.sqrt(len(runs))))
    cutoff = runs[-audit_runs][0]
    audit = [records[i] for i in held_out if i >= cutoff]
    audit_signatures = {transition_signature(row) for row in audit}
    audit_transitions = {(session_signature(row[0]), row[2], session_signature(row[3])) for row in audit}
    validation = [records[i] for i in held_out if i < cutoff
                  and transition_signature(records[i]) not in audit_signatures
                  and (session_signature(records[i][0]), records[i][2], session_signature(records[i][3])) not in audit_transitions]
    if not validation:
        validation = [records[i] for i in held_out if i < cutoff
                      and transition_signature(records[i]) not in audit_signatures]
    independent_runs = len(runs)
    minimum = max(1, math.ceil(math.log2(1. + independent_runs)) - 1)
    if min(len(training), len(validation), len(audit)) < minimum:
        return None
    return training, validation, audit


def verified_improvement(records, baseline, updated):
    if not records or len(records) != len(baseline) or len(records) != len(updated):
        return False
    by_scene = {}
    for row, before, after in zip(records, baseline, updated):
        if not (math.isfinite(before) and math.isfinite(after)):
            return False
        scene = session_signature(row[0])
        total, count = by_scene.get(scene, (0., 0))
        by_scene[scene] = (total + before - after, count + 1)
    changes = [total / count for total, count in by_scene.values()]
    wins = sum(delta > 0. for delta in changes)
    losses = sum(delta < 0. for delta in changes)
    tested = wins + losses
    if tested == 0 or wins <= losses or sum(changes) <= 0.:
        return False
    tail = sum(math.comb(tested, k) for k in range(wins, tested + 1))
    significance = 0.1 if tested < 8 else 0.05
    return tail / (1 << tested) < significance


def policy_regressed(previous, current, records):
    if previous is None or current is None:
        return False
    count = sum(row[2] != 0 and row[5] != 0. for row in records)
    if count < 2:
        return False
    delta = previous - current
    variance = (previous * (1. - previous) + current * (1. - current)) / count
    return delta > 0. and delta > math.sqrt(variance) * 1.6448536269514722


class ReplaySampler:
    def __init__(self, records, indices):
        self.indices = list(indices)
        scenes = [session_signature(records[i][0]) for i in self.indices]
        counts = Counter(scenes)
        influence = [abs(records[i][5]) + abs(1. - records[i][11]) + float(len(records[i]) > 13 and records[i][13]) for i in self.indices]
        typical = sum(influence) / max(1, len(influence))
        self.weights = [math.sqrt(1. + importance / max(sys.float_info.min, typical)) / math.sqrt(counts[scene]) for scene, importance in zip(scenes, influence)]

    def draw(self, count):
        size = min(max(0, int(count)), len(self.indices))
        if size == len(self.indices):
            return random.sample(self.indices, size)
        if not size:
            return []
        return [index for _, index in heapq.nsmallest(size, ((random.expovariate(weight), index) for weight, index in zip(self.weights, self.indices)))]


def observed_discount_rate(records):
    exposure = 0.
    endings = 0
    for row in records:
        if not row[12]:
            exposure += max(sys.float_info.epsilon, float(row[7]))
            endings += bool(row[6])
    return endings / exposure if exposure > 0. else 0.


def temporal_discount(duration, rate):
    return math.exp(-max(0., float(duration)) * max(0., float(rate)))


def multi_step_experience(records, index, discount_rate=None):
    first = records[index]
    total = 0.
    discount = 1.
    duration = 0.
    final = first
    if discount_rate is None:
        discount_rate = observed_discount_rate(records)
    horizon = max(1, int(math.log2(1. + len(records))))
    for offset in range(horizon):
        position = index + offset
        if position >= len(records):
            break
        row = records[position]
        if row[12] or (offset and (final[6] or row[1][-2:] != final[4][-2:] or (len(row) > 13 and row[13]) != (len(first) > 13 and first[13]))):
            break
        total += discount * row[5]
        duration += row[7]
        discount *= temporal_discount(row[7], discount_rate)
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
        cells = np.frombuffer(image, dtype=np.uint8).reshape(2, CHANNELS, VIS_H // CELL_H, CELL_H, VIS_W // CELL_W, CELL_W)
        return tuple(int(v) for v in (cells.sum(axis=(3, 5)) // (CELL_H * CELL_W)).transpose(0, 2, 3, 1).reshape(-1))
    out = []
    for scale in range(2):
        for y in range(0, VIS_H, CELL_H):
            for x in range(0, VIS_W, CELL_W):
                for channel in range(CHANNELS):
                    base = (scale * CHANNELS + channel) * PIXELS
                    out.append(sum(sum(image[base + (y + offset) * VIS_W + x:base + (y + offset) * VIS_W + x + CELL_W]) for offset in range(CELL_H)) // (CELL_H * CELL_W))
    return tuple(out)


def session_signature(image):
    cells = coarse_image_cells(image)
    return hashlib.blake2s(bytes(cells[:CELLS_PER_VIEW * CHANNELS]), digest_size=8).digest()


class TargetNavigator:
    def __init__(self):
        self.visits = Counter()
        self.outcomes = {}
        self.focus = None
        self.focus_key = None
        self.release_pending = False
        self.last_intent = None
        self.total = 0

    @staticmethod
    def identifier(x, y):
        return (round(float(x) * VIS_W / max(1, CELL_W)), round(float(y) * VIS_H / max(1, CELL_H)))

    def targets(self, points, meta):
        if not points:
            self.focus = None
            self.focus_key = None
            return ()
        mx, my = float(meta[4]), float(meta[5])
        distinct = {}
        for x, y, quality in points:
            if not (0. <= x <= 1. and 0. <= y <= 1.):
                continue
            key = self.identifier(x, y)
            old = distinct.get(key)
            if old is None or quality > old[2]:
                distinct[key] = (float(x), float(y), float(quality))
        ordered = []
        for point in distinct.values():
            x, y, kind = point
            key = self.identifier(x, y)
            attempts = self.visits[key]
            successes, tries = self.outcomes.get(key, (0., 0))
            confidence = (.5 + max(0., min(1., successes)) * tries) / (1. + tries)
            distance = math.hypot(*pointer_offset(x - mx, y - my, meta))
            persistence = 1. + (self.focus_key == key) / math.sqrt(1. + self.total)
            priority = (1. + max(0., kind)) * confidence * persistence / ((1. + math.sqrt(distance)) * math.sqrt(1. + attempts))
            ordered.append((priority, point))
        ordered.sort(reverse=True)
        if not ordered:
            self.focus = None
            self.focus_key = None
            return ()
        self.focus = ordered[0][1]
        self.focus_key = self.identifier(*self.focus[:2])
        return tuple(point for _, point in ordered)

    def guide(self, action, control, meta, held, steps):
        if self.release_pending and held.get('l'):
            self.release_pending = False
            self.last_intent = self.focus_key
            release = BUTTON_ACTIONS['l', False]
            return release, anchor_control(release)
        if self.release_pending:
            self.release_pending = False
        if self.focus is None or held.get('l') or held.get('r') or held.get('m'):
            return action, control
        if not (action == IDLE_ACTION or action in MOTION_ACTIONS or action == BUTTON_ACTIONS['l', True]):
            return action, control
        mx, my = meta[4], meta[5]
        dx, dy = pointer_offset(self.focus[0] - mx, self.focus[1] - my, meta)
        distance = math.hypot(dx, dy)
        reach = pointer_pixel_radius(meta)
        if distance <= reach and self.focus[2] > 0.:
            success, attempts = self.outcomes.get(self.focus_key, (0., 0))
            confidence = (.5 + max(0., min(1., success)) * attempts) / (1. + attempts)
            identifiable = self.focus[2] >= 1.
            if action == BUTTON_ACTIONS['l', True] or (identifiable and action == IDLE_ACTION and attempts and random.random() < confidence):
                self.release_pending = True
                self.last_intent = self.focus_key
                self.visits[self.focus_key] += 1
                press = BUTTON_ACTIONS['l', True]
                return press, anchor_control(press)
            return action, control
        if distance <= reach:
            return action, control
        if action in (BUTTON_ACTIONS['l', True], IDLE_ACTION):
            self.last_intent = self.focus_key
            action = min(MOTION_ACTIONS, key=lambda index: -((ACT[index][0] * dx + ACT[index][1] * dy) * ACT[index][2]))
        if action in MOTION_ACTIONS:
            direction_x, direction_y = dx / distance, dy / distance
            movement = list(anchor_control(action))
            learned = 1. - adaptive_exploration(steps, self.visits[self.focus_key])
            influence = max(0., 1. - learned)
            movement[0] = movement[0] * learned + direction_x * influence
            movement[1] = movement[1] * learned + direction_y * influence
            delay_fraction = max(0., min(1. - sys.float_info.epsilon, float(meta[14])))
            delay = delay_fraction / max(sys.float_info.epsilon, 1. - delay_fraction)
            aspect = max(0., min(1., float(meta[15])))
            relative_diagonal = math.hypot(aspect, 1. - aspect)
            target_speed = min(1., distance / max(sys.float_info.epsilon, delay * relative_diagonal))
            movement[2] = max(0., min(1., movement[2] * learned + target_speed * influence))
            return action, normalize_control(movement)
        return action, control

    def observe(self, reward, outcome):
        self.total += 1
        key = self.last_intent
        if key is None:
            return
        tries = self.visits[key]
        good, count = self.outcomes.get(key, (0., 0))
        effect = max(0., float(reward)) * max(0., min(1., float(outcome.get('efficacy', 1.))))
        if outcome.get('switches') or outcome.get('scroll'):
            count += 1
            good += (effect - good) / count
            self.outcomes[key] = (good, count)
            self.visits[key] = max(tries, count)
            self.last_intent = None
            self.focus = None
            self.focus_key = None
        elif len(self.outcomes) > REPLAY_LIMIT:
            self.outcomes.pop(min(self.outcomes, key=lambda k: self.visits[k]), None)


class Feedback:
    def __init__(self):
        self.frequency = {}
        self.sequence = deque(maxlen=max(2, math.isqrt(REPLAY_LIMIT)))
        self.background = None
        self.variance = 0.
        self.background_count = 0
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
        self.recent_states = deque(maxlen=max(2, math.isqrt(REPLAY_LIMIT)))
        self.progress_effects = 0
        self.demonstrated_goal_matches = 0
        self.demonstrated_pointer_advances = 0
        self.efficacy_total = 0.
        self.stagnant = 0
        self.loop_count = 0
        self.causal_total = 0.
        self.passive_context = {}
        self.action_context = {}
        self.state_value = {}
        self.causal_evidence = 0
        self.previous_passive = False
        try:
            self.numpy = importlib.import_module('numpy')
        except ImportError:
            self.numpy = None

    def reset_segment(self):
        self.sequence.clear()
        self.recent_states.clear()
        self.background = None
        self.variance = 0.
        self.background_count = 0
        self.previous_passive = False

    def difference(self, left, right):
        if len(left) != VIS_N or len(right) != VIS_N:
            raise ValueError('画面反馈维度不匹配')
        pixels = CHANNELS * PIXELS
        if self.numpy is not None:
            np = self.numpy
            a = np.frombuffer(left, dtype=np.uint8, count=pixels).astype(np.int16)
            b = np.frombuffer(right, dtype=np.uint8, count=pixels).astype(np.int16)
            return float(np.abs(a - b).mean()) / 255.
        return sum(abs(a - b) for a, b in zip(left[:pixels], right[:pixels])) / (pixels * 255.)

    def assess(self, old, new, previous, outcome, pointer, region):
        dist = self.difference(old, new)
        bg = self.difference(previous, old)
        if self.previous_passive:
            self.background_count += 1
            count = self.background_count
            old_background = self.background if self.background is not None else 0.
            delta = bg - old_background
            self.background = old_background + delta / count
            self.variance += (delta * (bg - self.background) - self.variance) / count
        count = max(1, self.background_count)
        changed = bool(outcome['changed'])
        self.previous_passive = not changed and not outcome['blocked']
        if not changed and not outcome['blocked']:
            self.passive_count += 1
            d = dist - self.passive_average
            self.passive_average += d / self.passive_count
            self.passive_variance += (d * (dist - self.passive_average) - self.passive_variance) / self.passive_count

        signature = session_signature(new)
        old_signature = session_signature(old)
        context = old_signature
        idle_mean, idle_var, idle_visits = self.passive_context.get(context, (0., 0., 0))
        ambient = max((self.background or 0.) + math.sqrt(max(0., self.variance)),
                      self.passive_average + math.sqrt(max(0., self.passive_variance)),
                      idle_mean + math.sqrt(max(0., idle_var)))
        pixel_resolution = 1. / (CHANNELS * PIXELS * 255.)
        impact = max(0., dist - ambient)
        noise_error = math.sqrt(max(0., self.variance) / count)
        scene_changed = old_signature != signature
        signal = changed and scene_changed and impact > max(pixel_resolution, noise_error)
        if not changed and not outcome['blocked']:
            idle_visits += 1
            d = dist - idle_mean
            idle_mean += d / idle_visits
            idle_var += (d * (dist - idle_mean) - idle_var) / idle_visits
            self.passive_context[context] = (idle_mean, max(0., idle_var), idle_visits)

        sightings = self.frequency.get(signature, 0)
        self.frequency[signature] = sightings + 1
        action = int(outcome.get('requested_action', outcome['action']))
        intended = outcome.get('intended_ctrl', outcome['ctrl'])
        control_key = bytes(max(0, min(15, round((float(v) + 1.) * 7.5))) for v in intended)
        current_action = (old_signature, control_key)
        self.sequence.append(current_action)
        repetition = self.sequence.count(current_action) / len(self.sequence)
        transition = (old_signature, signature)
        transition_visits = self.transition_frequency.get(transition, 0)
        reverse_visits = self.transition_frequency.get((signature, old_signature), 0)
        self.transition_frequency[transition] = transition_visits + 1
        repeating = self.recent_states.count(signature)
        recent_count = len(self.recent_states)
        repeated_fraction = repeating / recent_count if recent_count else 0.
        loop = bool(old_signature != signature and reverse_visits and repeated_fraction > 0.)
        self.recent_states.append(signature)

        efficacy = max(0., min(1., float(outcome.get('efficacy', 1.))))
        attributable = impact / max(dist, pixel_resolution) if signal else 0.
        novelty = 1. / math.sqrt(1. + transition_visits)
        prior_effect, prior_variance, prior_count = self.action_context.get((context, action), (0., 0., 0))
        confidence = prior_count / (1. + prior_count)
        consistency = 1. / (1. + abs(impact - prior_effect) / max(pixel_resolution, math.sqrt(max(0., prior_variance)), ambient)) if prior_count else 0.
        causal_strength = attributable * confidence * consistency
        old_value, old_seen = self.state_value.get(old_signature, (0., 0))
        new_value, new_seen = self.state_value.get(signature, (0., 0))
        discovery = attributable * (1. - confidence) * novelty
        persistence = max(0., 1. - repeated_fraction)
        state_advantage = max(0., new_value - old_value) * (new_seen / (1. + new_seen))
        reached = bool(outcome.get('goal_reached') and outcome.get('goal_demonstrated')) and signal and not loop
        goal_gain = attributable * persistence * float(reached)
        pointer_gain = max(0., min(1., float(outcome.get('demonstration_progress', 0.))))
        pointer_gain *= float(action in MOTION_ACTIONS and outcome.get('moved', 0.) > 0. and not outcome['blocked'])
        intrinsic_gain = (causal_strength + discovery * persistence + state_advantage * attributable) * novelty
        task_gain = goal_gain + pointer_gain
        gain = (intrinsic_gain + task_gain) * efficacy * float(not loop)
        if signal:
            n = prior_count + 1
            d = impact - prior_effect
            mean = prior_effect + d / n
            variance = prior_variance + (d * (impact - mean) - prior_variance) / n
            self.action_context[(context, action)] = (mean, max(0., variance), n)
        attempted = float(action != IDLE_ACTION and not outcome.get('pending_scroll'))
        failure = attempted * (1. - efficacy)
        failure += float(bool(outcome['blocked']))
        failure += float(not signal and not pointer_gain) * repetition * attempted
        failure += repeated_fraction * float(loop)
        failure += attempted * repetition * repeated_fraction * float((not signal and not pointer_gain) or new_seen >= old_seen and not pointer_gain)
        reward = math.tanh(gain - failure)
        progress = bool(signal and old_signature != signature and not loop and reward > 0. and efficacy > 0. and (reached or (prior_count > 1 and causal_strength > 0.)))
        self.demonstrated_goal_matches += int(reached and efficacy > 0.)
        self.demonstrated_pointer_advances += int(pointer_gain > 0. and not loop)
        current_value = (new_value * new_seen + max(0., reward) * float(progress)) / (new_seen + 1.)
        self.state_value[signature] = (current_value, new_seen + 1)
        self.stagnant = 0 if progress else self.stagnant + 1

        dynamics_key = (context, control_key)
        predicted, variance, seen = self.dynamics.get(dynamics_key, (0., 0., 0))
        deviation = abs(impact - predicted)
        n = seen + 1
        next_prediction = predicted + (impact - predicted) / n
        next_variance = variance + ((impact - predicted) * (impact - next_prediction) - variance) / n
        self.dynamics[dynamics_key] = (next_prediction, max(0., next_variance), n)
        self.prediction_error += deviation
        self.predictable_effects += int(bool(seen and deviation <= math.sqrt(max(variance, pixel_resolution ** 2))))
        self.total += 1
        self.effects += int(signal)
        self.blocks += int(bool(outcome['blocked']))
        self.repeats += int(loop or (not signal and repetition > 1. / math.sqrt(len(self.sequence))))
        self.progress_effects += int(progress)
        self.efficacy_total += efficacy
        self.causal_total += causal_strength
        self.causal_evidence += int(signal and prior_count > 0 and consistency > .5)
        self.loop_count += int(loop)
        for store in (self.frequency, self.transition_frequency, self.dynamics, self.passive_context, self.action_context, self.state_value):
            if len(store) > REPLAY_LIMIT:
                size = len(store) - REPLAY_LIMIT
                if store is self.frequency or store is self.transition_frequency:
                    discard = sorted(store, key=store.get)[:size]
                elif store is self.passive_context or store is self.action_context:
                    discard = sorted(store, key=lambda k: store[k][2])[:size]
                elif store is self.state_value:
                    discard = sorted(store, key=lambda k: store[k][1])[:size]
                else:
                    discard = sorted(store, key=lambda k: store[k][2])[:size]
                for key in discard:
                    store.pop(key, None)
        return reward, dist, progress


def read_replay(folder, slot):
    path = folder / f'experience.{slot}.gz'
    records = deque(maxlen=REPLAY_LIMIT)
    try:
        digest = hashlib.sha256()
        with gzip.open(path, 'rb') as f:
            head = f.read(len(REPLAY_MAGIC) + 12)
            if len(head) != len(REPLAY_MAGIC) + 12 or head[:len(REPLAY_MAGIC)] not in (REPLAY_MAGIC, REPLAY_LEGACY_MAGIC):
                raise ValueError('经验文件版本错误')
            compact = head[:len(REPLAY_MAGIC)] == REPLAY_MAGIC
            digest.update(head)
            count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
            if count > max(REPLAY_LIMIT * 8, 1024) or generation < 1:
                raise ValueError('经验标头异常')
            previous_next = None
            for _ in range(count):
                raw = f.read(REPLAY_PACK.size)
                if len(raw) != REPLAY_PACK.size:
                    raise ValueError('经验数据不完整')
                digest.update(raw)
                if compact:
                    flag = f.read(1)
                    if flag not in (b'\x00', b'\x01'):
                        raise ValueError('经验画面标记无效')
                    digest.update(flag)
                    if flag == b'\x01':
                        if previous_next is None:
                            raise ValueError('第一条经验不能复用前一画面')
                        ob = previous_next
                    else:
                        ob = f.read(VIS_N)
                        digest.update(ob)
                else:
                    ob = f.read(VIS_N)
                    digest.update(ob)
                    if previous_next is not None and ob == previous_next:
                        ob = previous_next
                nxt = f.read(VIS_N)
                if len(ob) != VIS_N or len(nxt) != VIS_N:
                    raise ValueError('经验画面数据不完整')
                digest.update(nxt)
                values = REPLAY_PACK.unpack(raw)
                action, executed_action, reward, done, dt, efficacy, reserved = values[:7]
                numeric = values[7:]
                demonstration = bool(executed_action & DEMONSTRATION_FLAG)
                executed_action &= ~DEMONSTRATION_FLAG
                if action >= ACT_N or executed_action >= ACT_N or not math.isfinite(reward) or not dt > 0. or not 0. <= efficacy <= 1. or not all(math.isfinite(v) for v in numeric):
                    raise ValueError('经验数值无效')
                meta = tuple(numeric[:META_N])
                nmeta = tuple(numeric[META_N:META_N * 2])
                ctrl = tuple(numeric[META_N * 2:META_N * 2 + CTRL_N])
                intended = tuple(numeric[META_N * 2 + CTRL_N:])
                records.append((ob, meta, action, nxt, nmeta, float(reward), bool(done), float(dt), ctrl, intended, executed_action, float(efficacy), bool(reserved), demonstration))
                previous_next = nxt
            if f.read(32) != digest.digest() or f.read(1):
                raise ValueError('经验校验失败')
        return records, generation
    except (OSError, EOFError, ValueError, struct.error, zlib.error, MemoryError):
        return None


def replay_sources(folder):
    headers = []
    for slot in (0, 1, 'recovery'):
        path = folder / f'experience.{slot}.gz'
        try:
            with gzip.open(path, 'rb') as source:
                head = source.read(len(REPLAY_MAGIC) + 12)
            if len(head) == len(REPLAY_MAGIC) + 12 and head[:len(REPLAY_MAGIC)] in (REPLAY_MAGIC, REPLAY_LEGACY_MAGIC):
                count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
                if 0 <= count <= max(REPLAY_LIMIT * 8, 1024) and generation > 0:
                    headers.append((generation, slot))
        except (OSError, EOFError, ValueError, struct.error, zlib.error):
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
        if len(header) == len(REPLAY_MAGIC) + 12 and header[:len(REPLAY_MAGIC)] in (REPLAY_MAGIC, REPLAY_LEGACY_MAGIC):
            _, recovered_generation = struct.unpack('<IQ', header[len(REPLAY_MAGIC):])
            if recovered_generation <= generation:
                path.unlink(missing_ok=True)
    except (OSError, ValueError, EOFError, struct.error, zlib.error):
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
                previous_next = None
                for row in entries:
                    ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved = row[:13]
                    encoded_action = executed_action | (DEMONSTRATION_FLAG if len(row) > 13 and row[13] else 0)
                    record = REPLAY_PACK.pack(action, encoded_action, reward, done, dt, efficacy, reserved, *meta, *nmeta, *ctrl, *intended)
                    reused = previous_next is not None and (ob is previous_next or ob == previous_next)
                    flag = b'\x01' if reused else b'\x00'
                    for payload in ((record, flag, nxt) if reused else (record, flag, ob, nxt)):
                        f.write(payload)
                        digest.update(payload)
                    previous_next = nxt
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
    except (OSError, ValueError, UnicodeError, zlib.error):
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
        self.closed = False
        self.backpressure = 0
        self.dropped = 0
        self.spill = deque(maxlen=max(4, 2 * math.isqrt(REPLAY_LIMIT)))
        self.spill_lock = threading.Lock()
        self.write_ms = deque(maxlen=96)
        self.queue_ms = deque(maxlen=96)
        self.pending = queue.Queue(maxsize=max(4, 2 * math.isqrt(REPLAY_LIMIT)))
        self.writer = threading.Thread(target=self._archive_job, daemon=True)
        self.writer.start()

    def _archive_job(self):
        while True:
            item = self.pending.get()
            try:
                if item is None:
                    return
                row, queued = item
                started = time.monotonic()
                self.queue_ms.append((started - queued) * 1000.)
                try:
                    self._remember(row)
                except Exception as error:
                    self.error = type(error).__name__ + ': ' + str(error)[:140]
                finally:
                    self.write_ms.append((time.monotonic() - started) * 1000.)
                with self.spill_lock:
                    overflow = self.spill.popleft() if self.spill else None
                if overflow is not None:
                    extra_row, extra_at = overflow
                    self.queue_ms.append((time.monotonic() - extra_at) * 1000.)
                    try:
                        self._remember(extra_row)
                    except Exception as error:
                        self.error = type(error).__name__ + ': ' + str(error)[:140]
                        self.dropped += 1
            finally:
                self.pending.task_done()

    @staticmethod
    def pack(row):
        ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed, efficacy, reserved = row[:13]
        encoded_action = executed | (DEMONSTRATION_FLAG if len(row) > 13 and row[13] else 0)
        header = REPLAY_PACK.pack(action, encoded_action, reward, done, dt, efficacy, reserved, *meta, *nmeta, *ctrl, *intended)
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
        demonstration = bool(executed & DEMONSTRATION_FLAG)
        executed &= ~DEMONSTRATION_FLAG
        if action >= ACT_N or executed >= ACT_N or not dt > 0. or not all(math.isfinite(v) for v in values[2:]):
            raise ValueError('长期经验记录无效')
        numeric = values[7:]
        return (data[REPLAY_PACK.size:REPLAY_PACK.size + VIS_N], tuple(numeric[:META_N]), action,
                data[REPLAY_PACK.size + VIS_N:], tuple(numeric[META_N:META_N * 2]),
                float(reward), bool(done), float(dt), tuple(numeric[META_N * 2:META_N * 2 + CTRL_N]),
                tuple(numeric[META_N * 2 + CTRL_N:]), executed, float(efficacy), bool(reserved), demonstration)

    def remember(self, row):
        if row[12] or self.closed:
            return
        try:
            self.pending.put_nowait((row, time.monotonic()))
        except queue.Full:
            self.backpressure += 1
            with self.spill_lock:
                if len(self.spill) == self.spill.maxlen:
                    self.dropped += 1
                self.spill.append((row, time.monotonic()))

    def _remember(self, row):
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
                demonstration = len(row) > 13 and row[13]
                should_keep = demonstration or visits == 1 or surprise or periodic or random.random() < 1. / math.sqrt(1. + visits)
                if not should_keep:
                    return
                priority = max(0., magnitude) + 1. / math.sqrt(visits) + max(0., float(row[11])) / math.sqrt(1. + visits) + float(demonstration)
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
            requested = min(max(0, int(count)), self.kept)
            if not requested:
                return []
            try:
                candidates_count = min(self.kept, max(requested * 8, 4 * math.ceil(math.log2(self.kept + 1))))
                priority_count = min(candidates_count, max(requested * 2, math.isqrt(candidates_count)))
                rows = {row[0]: row for row in self.db.execute(
                    'SELECT id,scene,priority FROM experiences INDEXED BY experiences_priority ORDER BY priority DESC LIMIT ?',
                    (priority_count,))}
                minimum, maximum = self.db.execute('SELECT min(id),max(id) FROM experiences').fetchone()
                if minimum is None:
                    return []
                for _ in range(candidates_count - priority_count):
                    pivot = random.randint(minimum, maximum)
                    match = self.db.execute('SELECT id,scene,priority FROM experiences WHERE id>=? ORDER BY id LIMIT 1', (pivot,)).fetchone()
                    if match is None:
                        match = self.db.execute('SELECT id,scene,priority FROM experiences ORDER BY id LIMIT 1').fetchone()
                    if match is not None:
                        rows[match[0]] = match
                if not rows:
                    return []
                grouped = Counter(row[1] for row in rows.values())
                typical = sum(max(0., float(row[2])) for row in rows.values()) / len(rows)
                typical = max(sys.float_info.min, typical)
                selected = []
                for row_id, scene, priority in rows.values():
                    if not math.isfinite(priority):
                        continue
                    weight = math.sqrt(1. + max(0., priority) / typical) / math.sqrt(grouped[scene])
                    key = math.log1p(-random.random()) / weight
                    if len(selected) < requested:
                        heapq.heappush(selected, (key, row_id))
                    elif key > selected[0][0]:
                        heapq.heapreplace(selected, (key, row_id))
                decoded = []
                for _, row_id in sorted(selected, reverse=True):
                    record = self.db.execute('SELECT data FROM experiences WHERE id=?', (row_id,)).fetchone()
                    if record is None:
                        continue
                    try:
                        row = self.unpack(record[0])
                        if not row[12]:
                            decoded.append(row)
                    except (ValueError, zlib.error, struct.error):
                        continue
                return decoded
            except (sqlite3.Error, OSError, ValueError, OverflowError) as error:
                self.error = str(error)[:140]
                return []

    def sync(self):
        self.pending.join()
        while True:
            with self.spill_lock:
                overflow = self.spill.popleft() if self.spill else None
            if overflow is None:
                break
            try:
                self._remember(overflow[0])
            except Exception as error:
                self.error = type(error).__name__ + ': ' + str(error)[:140]
                self.dropped += 1
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
            if self.closed:
                return
            self.closed = True
        self.sync()
        self.pending.put(None)
        self.writer.join()
        with self.lock:
            if self.db is not None:
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
        self.current_goal_demonstrated = False
        self.description = '发现可控状态'
        data = read_json(self.path, {})
        if isinstance(data, dict) and data.get('version') in (1, 2):
            try:
                self.states = {str(k): [int(v[0]), float(v[1])] for k, v in data.get('states', {}).items() if len(k) == 16 and len(v) == 2}
                self.edges = {str(k): {str(a): {str(dest): [int(v[0]), float(v[1]), float(v[2]), int(v[3]) if len(v) > 3 else 0]
                                        for dest, v in dests.items() if len(dest) == 16 and len(v) in (3, 4)}
                                         for a, dests in actions.items()} for k, actions in data.get('edges', {}).items() if len(k) == 16}
                self.total = max(0, int(data.get('total', 0)))
            except (TypeError, ValueError, KeyError, AttributeError):
                self.states, self.edges, self.total = {}, {}, 0

    def signature(self, image):
        cell = coarse_image_cells(image)
        quantized = bytes(max(0, min(15, (cell[index] + cell[index + 1] + cell[index + 2]) // 48)) for index in range(0, CELLS_PER_VIEW * CHANNELS, CHANNELS))
        return hashlib.blake2s(quantized, digest_size=8).hexdigest()

    def observe(self, old, action, new, reward, efficacy, progress, demonstration=False):
        source = self.signature(old)
        target = self.signature(new)
        with self.lock:
            self.total += 1
            old_state = self.states.setdefault(source, [0, 0.])
            old_state[0] += 1
            new_state = self.states.setdefault(target, [0, 0.])
            new_state[1] = max(new_state[1] * (1. - 1. / math.sqrt(1. + old_state[0])), max(0., reward) * efficacy * float(progress))
            destinations = self.edges.setdefault(source, {}).setdefault(str(action), {})
            entry = destinations.setdefault(target, [0, 0., 0., 0])
            entry[0] += 1
            entry[1] += float(reward)
            entry[2] += float(efficacy)
            entry[3] += int(bool(demonstration))
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
                self.current_goal = None
                self.current_goal_demonstrated = False
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
                    for next_state, (count, total_reward, total_effectiveness, demonstrations) in destinations.items():
                        if next_state not in self.states or count <= 0:
                            continue
                        likelihood = count / max(1, trials)
                        quality = total_effectiveness / count
                        next_probability = confidence * likelihood * quality
                        visit = self.states[next_state][0]
                        demonstrated_fraction = demonstrations / count
                        gain = (max(0., total_reward / count) + self.states[next_state][1] +
                                1. / math.sqrt(1. + visit)) * (1. + demonstrated_fraction)
                        gain *= next_probability / (1. + depth + (next_state == origin))
                        gain *= count / (count + math.sqrt(max(1, trials)))
                        if next_state != current and (best is None or gain > best[0]):
                            best = (gain, action if first_action is None else first_action, next_state,
                                    next_probability, depth + 1, demonstrations > 0)
                        if next_state not in seen and depth < horizon and next_probability > 0.:
                            heapq.heappush(frontier, (distance + 1. / max(.01, next_probability), depth + 1, next_state, action if first_action is None else first_action, next_probability))
            if best is None:
                self.current_goal = None
                self.current_goal_demonstrated = False
                self.description = f'复核已知状态 · {len(self.states)} 个状态'
                return None
            score, action, goal, confidence, length, demonstrated = best
            self.current_goal = goal
            self.current_goal_demonstrated = demonstrated
            self.description = f'自主规划 {length} 步目标 · 状态 {len(self.states)} · 路径可靠度 {confidence:.0%}'
            trust = confidence * (1. - adaptive_exploration(self.total, self.states[origin][0]))
            return (action, min(1., max(0., trust)), score)

    def save(self):
        with self.lock:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            save_json(self.path, {'version': 2, 'total': self.total, 'states': self.states, 'edges': self.edges})


class LiteBrain:
    def __init__(self, folder):
        self.folder = folder
        self.archive = LifelongMemory(folder)
        self.table = {}
        self.actor = {}
        self.visits = {}
        self.steps = 0
        self.discount_rate = 0.
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.control_evidence = ControlEvidence()
        self.generation = 0
        self.latest_replay_generation = 0
        self.slot = -1
        self.label = 'CPU · 自适应轻量后端'
        self.accelerated = False
        self.online_batches = 0
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
                    if len(keybytes) in (CELLS_PER_VIEW * 2 + 5, 14, 13) and len(numbers) == ACT_N and all(map(math.isfinite, numbers)):
                        table[keybytes] = numbers
                except (TypeError, ValueError, OverflowError):
                    continue
            for key, value in (data.get('actor') or {}).items() if isinstance(data.get('actor'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    numbers = [float(v) for v in value]
                    if len(keybytes) in (CELLS_PER_VIEW * 2 + 6, 15, 14) and len(numbers) == CTRL_N and all(math.isfinite(v) and -1. <= v <= 1. for v in numbers):
                        actor[keybytes] = list(normalize_control(numbers))
                except (TypeError, ValueError, OverflowError):
                    continue
            for key, value in (data.get('visits') or {}).items() if isinstance(data.get('visits'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    if len(keybytes) in (CELLS_PER_VIEW * 2 + 5, 14, 13) and isinstance(value, int) and not isinstance(value, bool) and value >= 0:
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
        self.discount_rate = observed_discount_rate(self.memory)
        self.control_evidence = ControlEvidence(self.memory)
        if self.memory and not self.archive.kept:
            for row in self.memory:
                self.archive.remember(row)

    def rebuild_from_memory(self):
        with self.save_lock:
            self.discount_rate = observed_discount_rate(self.memory)
            self.table.clear()
            self.actor.clear()
            self.visits.clear()
            for row in self.memory:
                if not row[12]:
                    self.update(row)

    def restore_experience(self, records, steps):
        with self.save_lock:
            self.memory = deque(records, maxlen=REPLAY_LIMIT)
            self.control_evidence = ControlEvidence(self.memory)
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
            tiles.append(b'T' + bytes([index]) + hashlib.blake2s(data + visual[index * 12:index * 12 + 12] + visual[CELLS_PER_VIEW + index * 12:CELLS_PER_VIEW + index * 12 + 12], digest_size=12).digest())
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
                return choice, self.control_evidence.explore(choice, meta)
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
        target = reward + (0. if done else temporal_discount(dt, self.discount_rate) * future)
        baseline = before[action] if before is not None else 0.
        if len(row) > 13 and row[13]:
            target = max(target, max(before or [0.]) + 1. / math.sqrt(1. + self.visits.get(keys[0], 0)))
        correction = (target - baseline) / math.sqrt(1. + self.visits.get(keys[0], 0))
        for key in keys:
            value = self.table.setdefault(key, [0.] * ACT_N)
            value[action] += correction
            self.visits[key] = self.visits.get(key, 0) + 1
            if len(row) > 11 and (reward > 0. or (len(row) > 13 and row[13])) and row[11] > 0.:
                actor_key = key + bytes([action])
                old = self.actor.get(actor_key, list(anchor_control(action)))
                efficacy = min(1., max(0., row[11]))
                rate = efficacy * (1. if len(row) > 13 and row[13] else max(0., reward)) / math.sqrt(1. + self.visits[key])
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

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
            row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration))
            self.memory.append(row)
            self.control_evidence.observe(row)
            self.steps += 1
        self.archive.remember(row)

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.train_memory if self.train_memory is not None else self.memory)
            indices = [i for i, row in enumerate(source) if not row[12]]
        if not indices:
            return 0
        total = 0
        archive_rows = self.archive.sample(min(max(2, int(math.sqrt(count))), max(2, len(indices)))) if self.train_memory is None else []
        sampler = ReplaySampler(source, indices)
        discount_rate = observed_discount_rate(source)
        for step in range(count):
            if stop.is_set():
                break
            if archive_rows and step % max(2, int(math.sqrt(len(indices)))) == 0:
                row = random.choice(archive_rows)
            else:
                row = multi_step_experience(source, sampler.draw(1)[0], discount_rate)
            with self.save_lock:
                if stop.is_set():
                    break
                self.discount_rate = discount_rate
                self.update(row)
                total += 1
        if self.train_memory is None:
            with self.save_lock:
                self.online_batches += total
        return total

    def policy_metric(self, records):
        useful = [row for row in records if row[2] != 0 and (row[5] != 0. or (len(row) > 13 and row[13]))]
        if len(useful) < 8:
            return None
        good = 0
        for row in useful:
            q = self.values(row[0], row[1]) or [0.] * ACT_N
            held = {'l': row[1][9] > .5, 'r': row[1][10] > .5, 'm': row[1][11] > .5}
            best = max(candidates(held), key=lambda a: q[a])
            good += (best == row[2]) if (row[5] > 0. or (len(row) > 13 and row[13])) else (best != row[2])
        return good / len(useful)

    def validation_targets(self, records):
        labels = []
        for row in records:
            after = self.values(row[3], row[4])
            held = {'l': row[4][9] > .5, 'r': row[4][10] > .5, 'm': row[4][11] > .5}
            future = max(after[a] for a in candidates(held)) if after else 0.
            labels.append(row[5] + (0. if row[6] else temporal_discount(row[7], self.discount_rate) * future))
        return labels

    def evaluation_losses(self, records, labels):
        losses = []
        for row, target in zip(records, labels):
            values = self.values(row[0], row[1])
            error = abs((values[row[2]] if values is not None else 0.) - target)
            losses.append((.5 * error * error if error < 1. else error - .5) + (max(0., max(values or [0.]) - (values[row[2]] if values is not None else 0.)) if len(row) > 13 and row[13] else 0.))
        return losses

    def evaluate(self, records, labels):
        return sum(self.evaluation_losses(records, labels)) / max(1, len(records))

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
            self.discount_rate = observed_discount_rate(self.train_memory)
            audit_labels = self.validation_targets(audit)
            audit_losses = self.evaluation_losses(audit, audit_labels)
            self.sleep_audit = (audit, audit_labels, sum(audit_losses) / len(audit), self.policy_metric(audit))
            labels = self.validation_targets(validation)
            baseline_losses = self.evaluation_losses(validation, labels)
            before = sum(baseline_losses) / len(validation)
            quality = self.policy_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits), baseline_losses)

    def abort_sleep(self):
        with self.save_lock:
            if self.sleep_evaluation is not None:
                self.table = self.sleep_evaluation[4]
                self.actor = self.sleep_evaluation[5]
                self.visits = self.sleep_evaluation[6]
            self.train_memory = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None

    def sleep_progress(self):
        with self.save_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality, snapshot, previous_actor, previous_visits, baseline_losses = self.sleep_evaluation
            losses = self.evaluation_losses(records, labels)
            after = sum(losses) / len(losses)
            current = self.policy_metric(records)
            if verified_improvement(records, baseline_losses, losses) and not policy_regressed(quality, current, records):
                if self.sleep_best is None or after < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits))
            return {'loss': after, 'verified': self.sleep_best is not None, 'best': self.sleep_best[0] if self.sleep_best is not None else None, 'baseline': before}

    def end_sleep(self):
        with self.save_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            evaluation = self.sleep_progress()
            after = evaluation['loss'] if evaluation is not None else float('nan')
            records, labels, before, quality, snapshot, previous_actor, previous_visits, baseline_losses = self.sleep_evaluation
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
                    if not math.isfinite(audit_after) or audit_after > audit_before or policy_regressed(audit_policy, audit_current, audit_rows):
                        self.table, self.actor, self.visits = snapshot, previous_actor, previous_visits
                        return False, before, audit_after, quality, audit_current
                return True, before, best[0], quality, best[1]
            self.table, self.actor, self.visits = snapshot, previous_actor, previous_visits
            degraded = not math.isfinite(after) or after > before or policy_regressed(quality, current, records)
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
        self.control_evidence = ControlEvidence()
        self.discount_rate = 0.
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
                self.vision = nn.Sequential(nn.Conv2d(CHANNELS * 2, 32, 5, stride=2, padding=2), nn.GELU(), nn.Conv2d(32, 48, 3, stride=2, padding=1), nn.GELU(), nn.Conv2d(48, 64, 3, stride=2, padding=1), nn.GELU(), nn.AdaptiveAvgPool2d((ENC_H, ENC_W)))
                self.visual_projection = nn.Sequential(nn.Flatten(), nn.Linear(64 * ENC_H * ENC_W, 160), nn.GELU())
                self.visual_attention = nn.Conv2d(64, 1, 1)
                self.visual_context = nn.Linear(64, 160)
                self.visual_norm = nn.LayerNorm(160)
                self.visual_growing = nn.ModuleList()
                self.reconstruction = nn.Sequential(nn.Linear(160 + META_N, 256), nn.GELU(), nn.Linear(256, CHANNELS * 2 * RECON_H * RECON_W), nn.Sigmoid())
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
        self.inference_durations = deque(maxlen=max(16, math.isqrt(REPLAY_LIMIT)))
        self.cuda_optimizer_steps = 0
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
        self.optq = torch.optim.AdamW(self.q.parameters())
        self.growth_at_step = 0
        self.growth_attempts = 0
        self.world_growth_at_step = 0
        self.visual_growth_at_step = 0
        free_bytes = 0
        if getattr(device, 'type', None) == 'cuda':
            try:
                free_bytes = torch.cuda.mem_get_info(device)[0]
            except RuntimeError:
                pass
        tensor_bytes_per_sample = 2 * VIS_N * torch.tensor([], dtype=torch.float32).element_size()
        theoretical_capacity = max(1, free_bytes // max(1, tensor_bytes_per_sample)) if free_bytes else REPLAY_LIMIT
        self.batch_limits = {False: min(REPLAY_LIMIT, theoretical_capacity), True: min(REPLAY_LIMIT, theoretical_capacity)}
        initial_batch = max(1, min(self.batch_limits[False], math.isqrt(REPLAY_LIMIT)))
        self.batch_sizes = {False: initial_batch, True: initial_batch}
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
                before_q = cpu_snapshot(self.t, self.q.state_dict())
                before_target = cpu_snapshot(self.t, self.target.state_dict())
                before_opt = cpu_snapshot(self.t, self.optq.state_dict())
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
        self.discount_rate = observed_discount_rate(self.memory)
        self.control_evidence = ControlEvidence(self.memory)
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

    def grow_from_evidence(self, records, validation=()):
        if not records or not validation:
            return False
        train_scenes = {session_signature(row[0]) for row in records}
        validation_scenes = {session_signature(row[0]) for row in validation}
        if len(validation_scenes) < max(2, math.isqrt(len(train_scenes))):
            return False
        diverse = len(train_scenes)
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
        if not (grow_layer or grow_model or grow_visual):
            return False
        if grow_model:
            ratio = self.dynamics_metric(validation)
            grow_model = ratio is not None and math.isfinite(ratio) and ratio >= 1.
        if grow_model:
            grow_layer = grow_visual = False
        elif grow_layer:
            grow_visual = False
        if not (grow_layer or grow_model or grow_visual):
            return False
        layer_parameters = (160 + META_N) * ((160 + META_N) * 2 + 1) + (160 + META_N) * 2 * ((160 + META_N) + 1) + 2 * (160 + META_N)
        world_parameters = sum(parameter.numel() for parameter in self.q.dynamics_alternative.parameters())
        visual_parameters = 64 * 2 + (64 * 128 + 128 * 64) * 9 + 128 + 64
        new_parameters = layer_parameters * int(grow_layer) + world_parameters * int(grow_model) + visual_parameters * int(grow_visual)
        scalar_bytes = self.t.tensor([], dtype=next(self.q.parameters()).dtype).element_size()
        optimizer_copies = 1 + (2 if isinstance(self.optq, self.t.optim.AdamW) else 0)
        needed = new_parameters * scalar_bytes * (2 + optimizer_copies)
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
            self.control_evidence = ControlEvidence(self.memory)
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
            self.control_evidence = ControlEvidence(self.memory)
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
        explore_now = random.random() < epsilon
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
                            future_values = self.q.policy(imagined)[:, list((IDLE_ACTION, *MOTION_ACTIONS))]
                            future_action = future_values.argmax(dim=1)
                            utility = future_values.gather(1, future_action[:, None]).squeeze(1)
                            advantage = (utility - utility.mean()).clamp(-scale, scale)
                            metric = metric + discount * planning_reliability * likelihood * advantage
                            discount *= self.planning_trust * temporal_discount(max(self.perf['inference_ms'] / 1000., sys.float_info.epsilon), self.discount_rate)
                            if discount < 1. / max(1., self.steps + self.grads):
                                break
                            control_options = self.q.policy_controls(imagined)[:, list((IDLE_ACTION, *MOTION_ACTIONS))]
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
        self.inference_durations.append(elapsed)
        if explore_now:
            action = explore_action(allowed, meta, self.steps, ob, targets)
            return action, self.control_evidence.explore(action, meta)
        return action, anchor_control(action, control, trust)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
            row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration))
            self.memory.append(row)
            self.control_evidence.observe(row)
            if not reserved:
                self.discount_rate = observed_discount_rate(self.memory)
            self.steps += 1
        self.archive.remember(row)

    def train(self, count, stop):
        with self.save_lock:
            source = list(self.train_memory if self.train_memory is not None else self.memory)
            indices = [i for i, row in enumerate(source) if not row[12]]
        if len(indices) < 2:
            return 0
        self.discount_rate = observed_discount_rate(source)
        if self.train_memory is None and len(indices) > max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1)))):
            width = max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1))))
            old = indices[:-width]
            indices = random.sample(old, min(len(old), max(1, width // 2))) + indices[-width:]
        sampler_key = (self.steps, len(source), len(indices), self.train_memory is not None)
        if self.sampler_key != sampler_key:
            self.sampler = ReplaySampler(source, indices)
            self.sampler_key = sampler_key
        if self.historical_refreshed < 0 or self.grads - self.historical_refreshed >= max(1, int(math.sqrt(1. + self.grads))):
            self.historical_samples = self.archive.sample(min(max(8, int(math.sqrt(len(indices)) * 2)), self.batch_sizes[False])) if self.train_memory is None else []
            self.historical_refreshed = self.grads
        with self.model_lock:
            pressure = memory_pressure()
            if pressure > .25:
                mode = self.train_memory is not None
                target_batch = max(1, int(self.batch_limits[mode] * (1. - pressure)))
                self.batch_sizes[mode] = min(self.batch_sizes[mode], target_batch)
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
            peak_baseline = 0
            if getattr(self.d, 'type', None) == 'cuda':
                peak_baseline = t.cuda.memory_allocated(self.d)
                t.cuda.reset_peak_memory_stats(self.d)
            requested_batch = min(self.batch_sizes[sleeping], len(indices))
            if not sleeping and self.interactive_budget:
                throughput = self.training_throughput[False]
                if throughput > 0.:
                    requested_batch = min(requested_batch, max(1, int(throughput * self.interactive_budget)))
                else:
                    requested_batch = min(requested_batch, max(1, int(math.sqrt(requested_batch))))
            if stop.is_set():
                break
            sampled = self.sampler.draw(requested_batch)
            immediate = [source[i] for i in sampled]
            batch = [multi_step_experience(source, i, self.discount_rate) for i in sampled]
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
            demonstration = t.tensor([len(row) > 13 and row[13] for row in immediate], dtype=t.float32, device=self.d)
            autonomous = 1. - demonstration
            autonomous_count = autonomous.sum().clamp(min=1.)
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
                for column, name in ((9, 'l'), (10, 'r'), (11, 'm')):
                    down = nmeta[:, column] > .5
                    mask[:, BUTTON_ACTIONS[name, True]] = down
                    mask[:, BUTTON_ACTIONS[name, False]] = ~down
                online = online.masked_fill(mask, -1e8)
                best = online.argmax(dim=1, keepdim=True)
                next_q, _, _ = self.target(future, nmeta)
                after = next_q.gather(1, best).squeeze(1)
                future_features = self.target(immediate_future, immediate_meta)[2]
                discount = t.exp(-dt * self.discount_rate) * (1 - done)
                targets = rew + discount * after
                effect_targets = immediate_reward
            visual_target = t.nn.functional.adaptive_avg_pool2d(state, (RECON_H, RECON_W))
            reconstructed = self.q.reconstruct(embedding).reshape_as(visual_target)
            visual_error = t.nn.functional.smooth_l1_loss(reconstructed, visual_target)
            horizontal_error = t.nn.functional.smooth_l1_loss(reconstructed[:, :, :, 1:] - reconstructed[:, :, :, :-1], visual_target[:, :, :, 1:] - visual_target[:, :, :, :-1])
            vertical_error = t.nn.functional.smooth_l1_loss(reconstructed[:, :, 1:] - reconstructed[:, :, :-1], visual_target[:, :, 1:] - visual_target[:, :, :-1])
            detail_weight = visual_target.flatten(2).std(dim=-1, unbiased=False).mean().detach()
            visual_loss = visual_error + detail_weight * (horizontal_error + vertical_error)
            temporal = (t.nn.functional.smooth_l1_loss(values, targets, reduction='none') * autonomous).sum() / autonomous_count
            effect_loss = (t.nn.functional.smooth_l1_loss(effectiveness, effect_targets, reduction='none') * autonomous).sum() / autonomous_count
            execution_loss = (t.nn.functional.smooth_l1_loss(execution, efficacy, reduction='none') * autonomous).sum() / autonomous_count
            futures = self.q.world_predictions(embedding, ctrl)
            predicted_future = futures.mean(dim=0)
            per_head = t.nn.functional.smooth_l1_loss(futures, future_features.detach().unsqueeze(0).expand_as(futures), reduction='none').mean(dim=-1)
            if len(batch) > 1:
                bootstrap = (t.rand_like(per_head) < 1. - math.exp(-1.)).to(per_head.dtype)
                bootstrap = bootstrap + (bootstrap.sum(dim=1, keepdim=True) == 0).to(bootstrap.dtype)
                weighted = bootstrap * autonomous.unsqueeze(0)
                dynamics_loss = (per_head * weighted).sum() / weighted.sum().clamp(min=1.)
            else:
                dynamics_loss = (per_head.mean(dim=0) * autonomous).sum() / autonomous_count
            evidence = (state - immediate_future).abs().mean(dim=(1, 2, 3)).detach() * efficacy * autonomous
            inverse_errors = t.nn.functional.cross_entropy(self.q.infer_action(embedding, future_features.detach()), acts, reduction='none')
            inverse_loss = (inverse_errors * evidence).sum() / evidence.sum().clamp(min=1e-6)
            if len(batch) > 1:
                projection = t.nn.functional.normalize(predicted_future, dim=-1)
                teachers = t.nn.functional.normalize(future_features.detach(), dim=-1)
                logits = (projection @ teachers.T) * math.sqrt(projection.shape[-1])
                signatures = [session_signature(row[3]) for row in immediate]
                duplicate = t.tensor([[i != j and signatures[i] == signatures[j] for j in range(len(signatures))] for i in range(len(signatures))], dtype=t.bool, device=self.d)
                contrastive_errors = t.nn.functional.cross_entropy(logits.masked_fill(duplicate, -1e4), t.arange(len(batch), device=self.d), reduction='none')
                contrastive_loss = (contrastive_errors * autonomous).sum() / autonomous_count
            else:
                contrastive_loss = dynamics_loss * 0.
            advantage = (immediate_reward - effectiveness.detach()).clamp(-1., 1.)
            good = t.sigmoid(advantage / immediate_reward.detach().std(unbiased=False).clamp(min=1e-4))
            desired = ctrl * efficacy[:, None] + intended * (1. - efficacy[:, None])
            auxiliary = ((predicted - desired).square().mean(dim=1) * (good * efficacy * autonomous + demonstration)).mean()
            imitation_loss = (t.nn.functional.cross_entropy(qvalues, acts, reduction='none') * demonstration).sum() / demonstration.sum().clamp(min=1.)
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
            loss = temporal + effect_loss + execution_loss + auxiliary + imitation_loss * demonstration.mean() + visual_weight * visual_loss + dynamics_weight * (dynamics_loss + inverse_loss + contrastive_loss) - confidence * actor_gain * autonomous.mean()
            if not bool(t.isfinite(loss).item()):
                raise ValueError('模型训练数值异常')
            if stop.is_set():
                break
            self.optq.zero_grad(set_to_none=True)
            if self.grad_scaler is not None:
                scale_before = self.grad_scaler.get_scale()
                self.grad_scaler.scale(loss).backward()
                self.grad_scaler.unscale_(self.optq)
                t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.0)
                self.grad_scaler.step(self.optq)
                self.grad_scaler.update()
                optimizer_updated = self.grad_scaler.get_scale() >= scale_before
            else:
                loss.backward()
                t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.0)
                self.optq.step()
                optimizer_updated = True
            if optimizer_updated:
                self.grads += 1
                if getattr(self.d, 'type', None) == 'cuda':
                    self.cuda_optimizer_steps += 1
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
                if previous > 0 and observed < previous and latency >= previous_latency > 0.:
                    proposed = max(1, int(proposed * observed / previous))
                elif not previous or observed >= previous or latency < previous_latency:
                    proposed += max(1, math.isqrt(proposed))
                if getattr(self.d, 'type', None) == 'cuda':
                    try:
                        free, total = t.cuda.mem_get_info(self.d)
                        peak = t.cuda.max_memory_allocated(self.d)
                        allocated = t.cuda.memory_allocated(self.d)
                        cached = max(0, t.cuda.memory_reserved(self.d) - allocated)
                        measured_per_sample = max(1, (peak - peak_baseline) // max(1, len(batch)))
                        transient = max(0, peak - allocated)
                        extra = max(0, free + cached - transient) // measured_per_sample
                        safe_limit = max(len(batch), len(batch) + extra)
                        self.batch_limits[sleeping] = max(1, min(REPLAY_LIMIT, safe_limit))
                        proposed = min(proposed, self.batch_limits[sleeping])
                    except RuntimeError:
                        pass
                self.batch_sizes[sleeping] = max(1, min(len(indices), self.batch_limits[sleeping], proposed))
            count_done += 1
        return count_done

    def evaluation_losses(self, entries, labels):
        self.q.eval()
        t = self.t
        losses = []
        with t.no_grad():
            evaluation_batch = max(1, self.batch_sizes[True])
            for start in range(0, len(entries), evaluation_batch):
                segment = entries[start:start + evaluation_batch]
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
                q_loss = t.nn.functional.smooth_l1_loss(qvalue, target, reduction='none')
                visual_target = t.nn.functional.adaptive_avg_pool2d(frames, (RECON_H, RECON_W)).flatten(1)
                visual_loss = t.nn.functional.smooth_l1_loss(self.q.reconstruct(features), visual_target, reduction='none').mean(dim=1)
                selected_controls = all_controls.gather(1, actions[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
                teacher = controls * efficacy[:, None] + intended * (1. - efficacy[:, None])
                actor_loss = (selected_controls - teacher).square().mean(dim=1) * efficacy
                effect_loss = t.nn.functional.smooth_l1_loss(self.q.effect_value(features, controls), rewards, reduction='none')
                execution_loss = t.nn.functional.smooth_l1_loss(self.q.execute_value(features, intended), efficacy, reduction='none')
                next_frames = self.images([row[3] for row in segment])
                next_meta = t.tensor([row[4] for row in segment], dtype=t.float32, device=self.d)
                next_features = self.target(next_frames, next_meta)[2]
                evidence = (frames - next_frames).abs().mean(dim=(1, 2, 3)) * efficacy
                inverse = t.nn.functional.cross_entropy(self.q.infer_action(features, next_features), actions, reduction='none')
                inverse_loss = inverse * evidence * (len(segment) / evidence.sum().clamp(min=1e-6))
                estimated, disagreement = self.q.predict_with_uncertainty(features, controls)
                dynamics_loss = t.nn.functional.smooth_l1_loss(estimated, next_features, reduction='none').mean(dim=1) + disagreement.sqrt()
                demonstration = t.tensor([len(row) > 13 and row[13] for row in segment], dtype=t.float32, device=self.d)
                imitation_loss = t.nn.functional.cross_entropy(values, actions, reduction='none') * demonstration
                segment_loss = (q_loss + effect_loss + execution_loss + dynamics_loss + inverse_loss) * (1. - demonstration) + actor_loss + visual_loss + imitation_loss
                losses.extend(segment_loss.cpu().tolist())
        return losses

    def evaluate(self, entries, labels):
        return sum(self.evaluation_losses(entries, labels)) / max(1, len(entries))

    def performance(self):
        with self.save_lock:
            training = self.training_throughput[self.train_memory is not None]
            metrics = {'world_models': 2 + len(self.q.world_models), 'transfer_ms': round(self.perf['transfer_ms'], 3), 'inference_ms': round(self.perf['inference_ms'], 3), 'training_samples_per_second': round(training, 2), 'batches': self.perf['batches'], 'training_examples': self.perf['training_examples'], 'visual_error': round(self.perf['visual_error'], 5), 'batch_size': self.batch_sizes[self.train_memory is not None], 'archive_count': self.archive.kept, 'archive_total_observed': self.archive.total, 'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'model_parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'planning_trust': round(self.planning_trust, 3), 'world_model_ratio': round(self.planning_ratio, 3) if self.planning_ratio is not None else None}
            if self.inference_durations:
                timings = sorted(self.inference_durations)
                metrics['inference_p95_ms'] = round(timings[int(.95 * (len(timings) - 1))], 3)
            if getattr(self.d, 'type', None) == 'cuda':
                metrics['cuda_model_validated'] = True
                metrics['cuda_optimizer_steps'] = self.cuda_optimizer_steps
                metrics['cuda_prior_training_steps'] = max(0, self.grads - self.cuda_optimizer_steps)
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
        records = [row for row in records if not (len(row) > 13 and row[13])]
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
        examples = [r for r in records if r[2] != 0 and (r[5] != 0. or (len(r) > 13 and r[13]))]
        if len(examples) < 8:
            return None
        total = 0
        with self.t.no_grad():
            evaluation_batch = max(1, self.batch_sizes[True])
            for start in range(0, len(examples), evaluation_batch):
                part = examples[start:start + evaluation_batch]
                q = self.q(self.images([r[0] for r in part]), self.t.tensor([r[1] for r in part], dtype=self.t.float32, device=self.d))[0].cpu().tolist()
                for row, scores in zip(part, q):
                    held = {'l': row[1][9] > .5, 'r': row[1][10] > .5, 'm': row[1][11] > .5}
                    chosen = max(candidates(held), key=lambda a: scores[a])
                    total += (chosen == row[2]) if (row[5] > 0. or (len(row) > 13 and row[13])) else (chosen != row[2])
        return total / len(examples)

    def validation_targets(self, records):
        t = self.t
        labels = []
        self.q.eval()
        with t.no_grad():
            evaluation_batch = max(1, self.batch_sizes[True])
            for start in range(0, len(records), evaluation_batch):
                segment = records[start:start + evaluation_batch]
                frames = self.images([row[3] for row in segment])
                next_meta = t.tensor([row[4] for row in segment], dtype=t.float32, device=self.d)
                online = self.q(frames, next_meta)[0]
                mask = t.zeros_like(online, dtype=t.bool)
                for column, name in ((9, 'l'), (10, 'r'), (11, 'm')):
                    down = next_meta[:, column] > .5
                    mask[:, BUTTON_ACTIONS[name, True]] = down
                    mask[:, BUTTON_ACTIONS[name, False]] = ~down
                online = online.masked_fill(mask, -1e8)
                best = online.argmax(dim=1, keepdim=True)
                after = self.target(frames, next_meta)[0].gather(1, best).squeeze(1)
                rewards = t.tensor([row[5] for row in segment], dtype=t.float32, device=self.d)
                ends = t.tensor([row[6] for row in segment], dtype=t.float32, device=self.d)
                durations = t.tensor([row[7] for row in segment], dtype=t.float32, device=self.d)
                labels.extend((rewards + (1 - ends) * t.exp(-durations * self.discount_rate) * after).cpu().tolist())
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
            self.discount_rate = observed_discount_rate(self.train_memory)
            self.grow_from_evidence(self.train_memory, validation)
            labels = self.validation_targets(validation)
            audit_labels = self.validation_targets(audit)
            audit_losses = self.evaluation_losses(audit, audit_labels)
            self.sleep_audit = (audit, audit_labels, sum(audit_losses) / len(audit), self.policy_metric(audit), self.effect_metric(audit), self.dynamics_metric(audit))
            baseline_losses = self.evaluation_losses(validation, labels)
            before = sum(baseline_losses) / len(validation)
            quality = self.policy_metric(validation)
            effect_before = self.effect_metric(validation)
            dynamics_before = self.dynamics_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, cpu_snapshot(self.t, self.q.state_dict()), cpu_snapshot(self.t, self.target.state_dict()), cpu_snapshot(self.t, self.optq.state_dict()), self.grads, effect_before, dynamics_before, baseline_losses)
            return {'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'world_models': 2 + len(self.q.world_models), 'parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'expanded': any(step == self.steps and step > 0 for step in (self.growth_at_step, self.world_growth_at_step, self.visual_growth_at_step))}

    def abort_sleep(self):
        with self.model_lock:
            if self.sleep_evaluation is not None:
                self.q.load_state_dict(self.sleep_evaluation[4])
                self.target.load_state_dict(self.sleep_evaluation[5])
                self.optq.load_state_dict(self.sleep_evaluation[6])
                self.grads = self.sleep_evaluation[7]
            self.train_memory = None
            self.sampler_key = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None
            self.rollback_sleep_capacity()

    def sleep_progress(self):
        with self.model_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality = self.sleep_evaluation[:4]
            losses = self.evaluation_losses(records, labels)
            after = sum(losses) / len(losses)
            current = self.policy_metric(records)
            effect_before = self.sleep_evaluation[8]
            effect_after = self.effect_metric(records)
            effect_ok = effect_before is None or (effect_after is not None and math.isfinite(effect_after) and effect_after <= effect_before)
            dynamics_before = self.sleep_evaluation[9]
            dynamics_after = self.dynamics_metric(records)
            dynamics_ok = dynamics_before is None or (dynamics_after is not None and math.isfinite(dynamics_after) and dynamics_after <= dynamics_before)
            if effect_ok and dynamics_ok and verified_improvement(records, self.sleep_evaluation[10], losses) and not policy_regressed(quality, current, records):
                if self.sleep_best is None or after < self.sleep_best[0]:
                    self.sleep_best = (after, current, cpu_snapshot(self.t, self.q.state_dict()), cpu_snapshot(self.t, self.target.state_dict()), cpu_snapshot(self.t, self.optq.state_dict()), self.grads)
            return {'loss': after, 'verified': self.sleep_best is not None, 'best': self.sleep_best[0] if self.sleep_best is not None else None, 'baseline': before}

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
            evaluation = self.sleep_progress()
            after = evaluation['loss'] if evaluation is not None else float('nan')
            records, labels, before, quality, old_q, old_target, old_opt, old_grads, old_effect, old_dynamics, baseline_losses = self.sleep_evaluation
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
                    if not math.isfinite(audit_after) or audit_after > audit_before or policy_regressed(audit_policy, audit_current, audit_rows) or (audit_effect is not None and (audit_new_effect is None or audit_new_effect > audit_effect)) or (audit_dynamics is not None and (audit_new_dynamics is None or audit_new_dynamics > audit_dynamics)):
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
            degraded = not math.isfinite(after) or after > before or policy_regressed(quality, current, records)
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


    def close(self):
        self.archive.close()


def cpu_snapshot(torch, obj):
    if torch.is_tensor(obj):
        return obj.detach().to('cpu', copy=True)
    if isinstance(obj, dict):
        return {key: cpu_snapshot(torch, value) for key, value in obj.items()}
    if isinstance(obj, (tuple, list)):
        return type(obj)(cpu_snapshot(torch, value) for value in obj)
    return copy.deepcopy(obj)


def validate_network(torch, engine, device):
    model = engine.q
    model.train()
    sample = bytes((i * 29) % 256 for i in range(VIS_N))
    frames = engine.images([sample])
    meta = torch.zeros((1, META_N), dtype=torch.float32, device=device)
    controls = torch.tensor([anchor_control(IDLE_ACTION)], dtype=torch.float32, device=device)
    try:
        model.zero_grad(set_to_none=True)
        with engine.autocast():
            logits, predicted, features = model(frames, meta)
            reconstruction = model.reconstruct(features.float())
            predicted_features, disagreement = model.predict_with_uncertainty(features.float(), controls)
            loss = (logits.float().square().mean() + predicted.float().square().mean() +
                    model.effect_value(features.float(), controls).square().mean() +
                    model.execute_value(features.float(), controls).square().mean() +
                    torch.nn.functional.smooth_l1_loss(predicted_features, features.detach().float()) +
                    disagreement.mean() + reconstruction.square().mean() +
                    model.infer_action(features.float(), features.detach().float()).square().mean())
        if not bool(torch.isfinite(loss).item()):
            raise ValueError('神经网络前向计算产生非法数值')
        loss.backward()
        for parameter in model.parameters():
            if parameter.grad is not None and not bool(torch.isfinite(parameter.grad).all().item()):
                raise ValueError('神经网络反向计算产生非法梯度')
        if getattr(device, 'type', None) == 'cuda':
            target_parameter = next((p for p in model.parameters() if p.grad is not None and
                                     bool(torch.count_nonzero(p.grad).item())), None)
            if target_parameter is None:
                raise ValueError('CUDA 模型计算未产生可供更新的梯度')
            original_parameter = target_parameter.detach().clone()
            try:
                trial = torch.optim.AdamW((target_parameter,), lr=0.001)
                trial.step()
                torch.cuda.synchronize(device)
                if not bool(torch.isfinite(target_parameter).all().item()):
                    raise ValueError('CUDA 优化器产生非法参数')
                if bool(torch.equal(original_parameter, target_parameter)):
                    raise ValueError('CUDA 优化器未实际更新网络参数')
            finally:
                with torch.no_grad():
                    target_parameter.copy_(original_parameter)
                torch.cuda.synchronize(device)
    finally:
        model.zero_grad(set_to_none=True)
        model.eval()
        del frames, meta, controls

def prepare_cuda_visibility(backend):
    if backend != 'cuda':
        return False
    value = os.environ.get('CUDA_VISIBLE_DEVICES')
    if value is not None and value.strip().lower() in ('', '-1', 'none', 'void'):
        os.environ.pop('CUDA_VISIBLE_DEVICES', None)
        return True
    return False


def hardware_probe(backend, folder):
    prepare_cuda_visibility(backend)
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
                passed = True
            except Exception as error:
                sys.stderr.write(str(device) + ' ' + type(error).__name__ + ': ' + str(error)[:160] + '\n')
        return passed
    except Exception as error:
        sys.stderr.write(type(error).__name__ + ': ' + str(error)[:160] + '\n')
    return False


def restore_shared_frames(operation, payload, frames):
    if not isinstance(payload, tuple) or not payload or payload[0] != SHARED_FRAME_TOKEN:
        return payload
    if frames is None:
        raise RuntimeError('共享画面缓冲区不可用')
    if operation == 'choose' and len(payload) == 4:
        return (bytes(frames.buf[:VIS_N]), *payload[1:])
    if operation == 'learn' and len(payload) in (12, 13):
        return (bytes(frames.buf[:VIS_N]), *payload[1:3], bytes(frames.buf[VIS_N:2 * VIS_N]), *payload[3:])
    raise ValueError('共享画面指令结构异常')


def torch_engine_main(channel, folder_name, runtime_name, backend, cancel_event, preempt_event, shared_name=None):
    shared_frames = None
    try:
        prepare_cuda_visibility(backend)
        if shared_name:
            shared_frames = shared_memory.SharedMemory(name=shared_name)
        if runtime_name:
            sys.path.insert(0, runtime_name)
        importlib.invalidate_caches()
        torch = importlib.import_module('torch')
        if backend == 'cuda':
            if getattr(torch.version, 'cuda', None) is None:
                raise RuntimeError('当前导入的 PyTorch 为不含 CUDA 的构建，正在尝试匹配 NVIDIA 驱动的专用版本')
            if not torch.cuda.is_available():
                raise RuntimeError('当前 PyTorch CUDA 构建为 ' + str(torch.version.cuda) + '，驱动或 GPU 初始化未通过；NVIDIA 设备详情：' + str(nvidia_driver_info()[:1]))
            indices = list(range(torch.cuda.device_count()))
            def available_memory(index):
                try:
                    return torch.cuda.mem_get_info(index)[0]
                except Exception:
                    return 0
            indices.sort(key=available_memory, reverse=True)
            devices = [(torch.device('cuda:' + str(i)), 'NVIDIA CUDA ' + str(torch.version.cuda) + ' · ' + torch.cuda.get_device_name(i)) for i in indices]
        elif backend == 'directml':
            directml = importlib.import_module('torch_directml')
            devices = [(directml.device(i), 'GPU · DirectML · ' + (directml.device_name(i) if hasattr(directml, 'device_name') else str(i + 1))) for i in range(directml.device_count())]
        else:
            torch.set_num_threads(max(1, (getattr(os, 'process_cpu_count', None) or os.cpu_count)() or 1))
            devices = [(torch.device('cpu'), 'CPU · PyTorch')]
        engine = None
        diagnostics = []
        for device, title in devices:
            candidate = None
            try:
                candidate = TorchBrain(Path(folder_name), torch, device, title)
                try:
                    validate_network(torch, candidate, device)
                except (RuntimeError, ValueError):
                    if not (candidate.use_bfloat16 or candidate.use_float16):
                        raise
                    candidate.use_bfloat16 = False
                    candidate.use_float16 = False
                    candidate.grad_scaler = None
                    if getattr(device, 'type', None) == 'cuda':
                        torch.cuda.empty_cache()
                    validate_network(torch, candidate, device)
                engine = candidate
                break
            except Exception as error:
                diagnostics.append(str(title) + '：' + str(error)[:160])
                if candidate is not None:
                    try:
                        candidate.close()
                    except Exception:
                        pass
                if getattr(device, 'type', None) == 'cuda':
                    try:
                        torch.cuda.empty_cache()
                    except RuntimeError:
                        pass
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
                    result = engine.choose(*restore_shared_frames(operation, payload, shared_frames))
                elif operation == 'learn':
                    engine.learn(*restore_shared_frames(operation, payload, shared_frames))
                    result = None
                elif operation == 'train':
                    batches, budget = payload if isinstance(payload, tuple) else (payload, None)
                    engine.interactive_budget = budget
                    trained = engine.train(batches, AnyStop(cancel_event, preempt_event))
                    result = (trained, engine.performance())
                elif operation == 'begin_sleep':
                    result = engine.begin_sleep()
                    if isinstance(result, dict):
                        result['batch_size'] = engine.batch_sizes[True]
                elif operation == 'end_sleep':
                    result = engine.end_sleep()
                elif operation == 'sleep_progress':
                    result = engine.sleep_progress()
                elif operation == 'abort_sleep':
                    engine.abort_sleep()
                    result = None
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
        if shared_frames is not None:
            try:
                shared_frames.close()
            except (OSError, BufferError):
                pass
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
        self.inference_observations = 0
        self.inference_wait = deque(maxlen=96)
        self.latest_perf = {}
        self.online_train_cost = 0.
        self.online_train_deferrals = 0
        self.sleeping = False
        self.latest_capacity = None
        self.closed = False
        self.failed = False
        self.sequence = 0
        ctx = mp.get_context('spawn')
        self.train_cancel = ctx.Event()
        self.train_preempt = ctx.Event()
        self.shared_frames = None
        try:
            self.shared_frames = shared_memory.SharedMemory(create=True, size=2 * VIS_N)
        except (OSError, BufferError, MemoryError):
            pass
        self.channel, endpoint = ctx.Pipe()
        self.process = ctx.Process(target=torch_engine_main, args=(endpoint, str(folder), str(runtime) if runtime is not None else None, backend, self.train_cancel, self.train_preempt, self.shared_frames.name if self.shared_frames is not None else None), daemon=True)
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
            self.model_verified = True
            engine_generation = self.generation
            latest = newest_replay(folder)
            recovered = [latest] if latest is not None else []
            if recovered:
                generation, slot, records = recovered[0]
                self.latest_replay_generation = generation
                self.memory = deque(records[-REPLAY_LIMIT:], maxlen=REPLAY_LIMIT)
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
                shared = self.shared_frames
                if shared is not None and isinstance(payload, tuple):
                    if operation == 'choose' and len(payload) == 4 and isinstance(payload[0], bytes) and len(payload[0]) == VIS_N:
                        shared.buf[:VIS_N] = payload[0]
                        payload = (SHARED_FRAME_TOKEN, *payload[1:])
                    elif operation == 'learn' and len(payload) in (13, 14) and isinstance(payload[0], bytes) and isinstance(payload[3], bytes) and len(payload[0]) == len(payload[3]) == VIS_N:
                        shared.buf[:VIS_N] = payload[0]
                        shared.buf[VIS_N:2 * VIS_N] = payload[3]
                        payload = (SHARED_FRAME_TOKEN, *payload[1:3], *payload[4:])
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
        if self.inference_observations > 0:
            if self.inference_interval <= 0.:
                self.inference_interval = interval
            else:
                self.inference_interval += (interval - self.inference_interval) / math.sqrt(1. + self.inference_observations)
        self.inference_observations += 1
        try:
            result = self._request('choose', (ob, meta, held, targets), timeout=15)
            self.inference_wait.append(time.monotonic() - started)
            return result
        finally:
            elapsed = time.monotonic() - started
            self.recent_inference_cost += (elapsed - self.recent_inference_cost) / math.sqrt(1. + self.steps)
            self.recent_inference = time.monotonic()
            self.inference_pending.clear()
            self.train_preempt.clear()

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
        data = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration))
        self.inference_pending.set()
        self.train_preempt.set()
        try:
            self._request('learn', data, timeout=15)
            with self.save_lock:
                self.memory.append(data)
                self.steps += 1
        finally:
            self.inference_pending.clear()
            self.train_preempt.clear()

    def train(self, count, stop):
        if stop.is_set() or self.train_cancel.is_set() or self.inference_pending.is_set() or self.train_preempt.is_set():
            return 0
        if not self.sleeping and self.inference_interval > 0.:
            idle = max(0., time.monotonic() - self.recent_inference)
            allowed = self.inference_interval - idle - self.recent_inference_cost
            if allowed <= 0. or (self.online_train_cost and self.online_train_cost >= allowed):
                self.online_train_deferrals += 1
                return 0
        if not self.rpc_lock.acquire(blocking=False):
            return 0
        try:
            if self.inference_pending.is_set() or self.train_preempt.is_set():
                return 0
            batches = min(max(1, int(count)), max(1, int(4 * math.sqrt(math.log2(2. + len(self.memory))))) if self.sleeping else 1)
            if not self.sleeping and self.inference_interval and time.monotonic() - self.recent_inference >= self.inference_interval:
                return 0
            if self.sleeping:
                budget = None
            else:
                measured = sorted(self.inference_wait)
                typical = measured[len(measured) // 2] if measured else (self.recent_inference_cost or self.inference_interval)
                budget = max(sys.float_info.epsilon, min(self.inference_interval or typical, typical))
            samples_per_second = self.latest_perf.get('training_samples_per_second', 0.)
            estimated = (batches * max(1, self.latest_perf.get('batch_size', 1)) / samples_per_second) if samples_per_second else 0.
            started = time.monotonic()
            result, perf = self._request('train', (batches, budget), timeout=max(45., 4. * estimated + self.recent_inference_cost))
            elapsed = time.monotonic() - started
            if not self.sleeping:
                self.online_train_cost = elapsed if not self.online_train_cost else .8 * self.online_train_cost + .2 * elapsed
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

    def abort_sleep(self):
        try:
            self._request('abort_sleep', timeout=45)
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
            try:
                alive = self.process.is_alive()
            except (AssertionError, ValueError):
                alive = False
            if alive:
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
            if self.shared_frames is not None:
                try:
                    self.shared_frames.close()
                finally:
                    try:
                        self.shared_frames.unlink()
                    except FileNotFoundError:
                        pass
                self.shared_frames = None


if os.name == 'nt':
    from ctypes import wintypes
    u = ctypes.WinDLL('user32', use_last_error=True)
    g = ctypes.WinDLL('gdi32', use_last_error=True)

    class POINT(ctypes.Structure):
        _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

    class RECT(ctypes.Structure):
        _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long), ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

    class LASTINPUTINFO(ctypes.Structure):
        _fields_ = [('cbSize', wintypes.UINT), ('dwTime', wintypes.DWORD)]

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
    u.GetLastInputInfo.argtypes = (ctypes.POINTER(LASTINPUTINFO),)
    u.GetLastInputInfo.restype = wintypes.BOOL
    u.OpenInputDesktop.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    u.OpenInputDesktop.restype = wintypes.HANDLE
    u.GetThreadDesktop.argtypes = (wintypes.DWORD,)
    u.GetThreadDesktop.restype = wintypes.HANDLE
    u.CloseDesktop.argtypes = (wintypes.HANDLE,)
    u.CloseDesktop.restype = wintypes.BOOL
    u.GetUserObjectInformationW.argtypes = (wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD))
    u.GetUserObjectInformationW.restype = wintypes.BOOL
    KBDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)
    MSPROC = KBDPROC

    class KBDLLHOOKSTRUCT(ctypes.Structure):
        _fields_ = [('vkCode', wintypes.DWORD), ('scanCode', wintypes.DWORD), ('flags', wintypes.DWORD), ('time', wintypes.DWORD), ('extra', ctypes.c_size_t)]

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
    kernel32.GetTickCount64.restype = ctypes.c_ulonglong
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
                executable = buf.value.casefold()
                identity_part = ('|' + identity[:160]) if Path(executable).name in ('chrome.exe', 'msedge.exe', 'firefox.exe', 'brave.exe', 'opera.exe', 'vivaldi.exe') else ''
                return executable + '|' + classname.value.casefold() + identity_part
        finally:
            kernel32.CloseHandle(process)
    return (classname.value.casefold() + '|' + identity) if classname.value else identity


def migrate_default_data(source, destination):
    source = Path(source)
    destination = Path(destination)
    if not source.exists():
        return False
    old, new = source.resolve(), destination.resolve()
    if old == new or old in new.parents or new in old.parents:
        return False
    if destination.exists() and any(destination.iterdir()):
        return False
    entries = list(source.iterdir())
    if not entries:
        return False
    destination.mkdir(parents=True, exist_ok=True)
    moved = []
    try:
        for entry in entries:
            target = destination / entry.name
            if target.exists():
                raise FileExistsError(str(target))
            shutil.move(str(entry), str(target))
            moved.append((entry, target))
    except (OSError, shutil.Error):
        for original, relocated in reversed(moved):
            try:
                shutil.move(str(relocated), str(original))
            except (OSError, shutil.Error):
                pass
        raise
    try:
        source.rmdir()
    except OSError:
        pass
    return True


def environment_for(folder, hwnd, display_name):
    descriptor = display_name.rsplit('  [0x', 1)[0].strip().casefold()
    descriptor = window_fingerprint(hwnd, descriptor)
    digest = hashlib.sha256(descriptor.encode('utf-8')).digest()
    code = tuple((int.from_bytes(digest[i:i + 4], 'little') / 4294967295.) * 2. - 1. for i in (0, 4))
    return Path(folder) / 'environments' / digest.hex()[:24], code


def system_idle_seconds():
    if os.name != 'nt':
        return None
    try:
        record = LASTINPUTINFO()
        record.cbSize = ctypes.sizeof(record)
        if not u.GetLastInputInfo(ctypes.byref(record)):
            return None
        elapsed = ((int(kernel32.GetTickCount64()) & 0xffffffff) - int(record.dwTime)) & 0xffffffff
        return elapsed / 1000. if elapsed < 0x80000000 else None
    except (OSError, AttributeError, ValueError):
        return None


def interactive_desktop():
    if os.name != 'nt':
        return False
    input_desktop = u.OpenInputDesktop(0, False, 0x0001)
    if not input_desktop:
        return False
    try:
        thread_desktop = u.GetThreadDesktop(kernel32.GetCurrentThreadId())
        if not thread_desktop:
            return False
        def desktop_name(handle):
            buffer = ctypes.create_unicode_buffer(256)
            length = wintypes.DWORD()
            if not u.GetUserObjectInformationW(handle, 2, buffer, ctypes.sizeof(buffer), ctypes.byref(length)):
                return None
            return buffer.value.casefold()
        current_name = desktop_name(input_desktop)
        thread_name = desktop_name(thread_desktop)
        return bool(current_name and thread_name and current_name == thread_name and u.GetForegroundWindow())
    finally:
        u.CloseDesktop(input_desktop)


def send_mouse(flags, data=0, dx=0, dy=0, stop=None):
    if stop is not None and stop.is_set():
        raise InterruptedError('已停止鼠标控制')
    packet = INPUT()
    packet.type = 0
    packet.data.mi = MOUSEINPUT(int(dx), int(dy), ctypes.c_uint32(data).value, flags, 0, AI_INPUT_MARK)
    if u.SendInput(1, ctypes.byref(packet), ctypes.sizeof(INPUT)) != 1:
        raise OSError(ctypes.get_last_error(), 'Windows 拒绝鼠标输入；请检查目标窗口权限和桌面状态')


def send_cursor(px, py, stop=None):
    if stop is not None and stop.is_set():
        raise InterruptedError('已停止鼠标控制')
    left = u.GetSystemMetrics(76)
    top = u.GetSystemMetrics(77)
    width = u.GetSystemMetrics(78)
    height = u.GetSystemMetrics(79)
    if width <= 0 or height <= 0:
        raise RuntimeError('无法读取虚拟桌面边界')
    nx = round((px - left) * 65535 / max(1, width - 1))
    ny = round((py - top) * 65535 / max(1, height - 1))
    send_mouse(0x8001 | 0x4000, dx=max(0, min(65535, nx)), dy=max(0, min(65535, ny)), stop=stop)


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
        self.human_guard = None
        self.user_override = threading.Event()
        self.input_generation = -1
        self.input_generation_guard = None
        self.exploration_targets = ()
        self.velocity = (0., 0.)
        self.motion_scale = 1.
        self.grabber = None
        self.grabber_errors = 0
        self.capture_failures = {'wgc': 0, 'dxcam': 0, 'gdi': 0}
        self.capture_quality = {name: {'mean_ms': 0., 'samples': 0, 'bad': 0} for name in ('wgc', 'dxcam', 'gdi')}
        self.capture_selected_at = 0.
        self.wgc_probe_at = 0.
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
        self.capture_preference = 'auto'
        self.capture_recovery = ''
        self.last_capture_ms = 0.
        self.capture_epoch = 0
        self.last_frame_backend = None
        self.last_frame_valid = True
        self.last_capture_stamp = 0.
        self.capture_metadata = []
        self.frozen_wgc = None
        self.frozen_dxcam = None
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
        g.SetStretchBltMode(self.mem, 4)
        self.down = {'l': False, 'r': False, 'm': False}
        self.hold_since = {}
        self.hold_last_motion = {}
        self.scroll_credit = 0.
        self.last_ai_cursor = None
        self.hold_history = deque(maxlen=96)
        self.wgc_retry_at = 0.
        try:
            display_hz = int(g.GetDeviceCaps(self.src, 116))
        except (OSError, ValueError, AttributeError):
            display_hz = 0
        self.display_period = 1. / display_hz if display_hz > 1 else 0.
        self.halted = threading.Event()
        self.release_uncertain = False
        self.enable_wgc()

    def enable_wgc(self):
        if self.wgc is not None or self.wgc_control is not None:
            return self.wgc_control is not None
        now = time.monotonic()
        if now < self.wgc_retry_at:
            return False
        self.wgc_retry_at = now + max(2., math.sqrt(1. + self.capture_epoch))
        try:
            windows_capture = importlib.import_module('windows_capture')
            interval_ms = max(1, round(self.display_period * 1000.)) if self.display_period else None
            source = windows_capture.WindowsCapture(window_hwnd=self.hwnd, cursor_capture=False, draw_border=False, minimum_update_interval=interval_ms)
            @source.event
            def on_frame_arrived(frame, capture_control):
                with self.wgc_lock:
                    current = time.monotonic()
                    if self.wgc_stamp and current > self.wgc_stamp:
                        self.wgc_periods.append(current - self.wgc_stamp)
                    self.wgc_frame = frame.frame_buffer.copy()
                    self.wgc_stamp = current
                    self.wgc_frame_id += 1
            @source.event
            def on_closed():
                with self.wgc_lock:
                    self.wgc_frame = None
                    self.wgc_stamp = 0.
                    self.wgc_frame_id += 1
                    self.capture_preference = 'dxcam' if self.grabber is not None else 'gdi'
                    self.capture_recovery = 'WGC 会话结束，已启用备用采集'
            control = source.start_free_threaded()
            self.wgc = source
            self.wgc_control = control
            self.capture_epoch += 1
            return True
        except Exception:
            self.wgc = None
            self.wgc_control = None
            return False

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
        if w < 8 or h < 8:
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
        explorables = []
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
                    if any(tag in category for tag in ('button', 'tabcontrol', 'link')):
                        explorables.append((left, top, right, bottom, 'click'))
                    elif any(tag in category for tag in ('scrollbar', 'listbox', 'listview', 'treeview')):
                        explorables.append((left, top, right, bottom, 'scroll'))
            except (OSError, ValueError):
                pass
            return True
        callback = WNDPROC(visit)
        u.EnumChildWindows(self.hwnd, callback, 0)
        self.target_cache = tuple(found)
        self.exploration_targets = tuple(explorables)
        self.target_region = region
        self.target_scan_at = now + interval
        return self.target_cache

    def explorable_controls(self, position, held):
        px, py = position
        result = set()
        for left, top, right, bottom, kind in self.exploration_targets:
            if left <= px < right and top <= py < bottom:
                if kind == 'click' and not held.get('l', False):
                    result.add(BUTTON_ACTIONS[('l', True)])
                if kind == 'scroll':
                    result.update(SCROLL_ACTIONS)
        return result

    def visible_targets(self, frame):
        if frame is None or len(frame) != VIS_N:
            return ()
        gap_x = max(4, VIS_W // max(12, int(math.sqrt(PIXELS / 100))))
        gap_y = max(4, VIS_H // max(8, int(math.sqrt(PIXELS / 100))))
        scores = []
        p = PIXELS
        for y in range(gap_y, VIS_H - gap_y, gap_y):
            for x in range(gap_x, VIS_W - gap_x, gap_x):
                offset = y * VIS_W + x
                horizontal = offset + gap_x
                vertical = offset + gap_y * VIS_W
                strength = sum(abs(frame[offset + p * c] - frame[horizontal + p * c]) + abs(frame[offset + p * c] - frame[vertical + p * c]) for c in range(CHANNELS))
                if strength:
                    scores.append((strength, (x + gap_x / 2) / VIS_W, (y + gap_y / 2) / VIS_H))
        if not scores:
            return ()
        ordered = sorted(item[0] for item in scores)
        typical = ordered[len(ordered) // 2]
        dispersion = sum(abs(item - typical) for item in ordered) / len(ordered)
        threshold = typical + dispersion
        proposals = []
        separation = math.hypot(gap_x / VIS_W, gap_y / VIS_H)
        for strength, x, y in sorted(scores, reverse=True):
            if strength <= threshold:
                break
            if any(math.hypot(x - a, y - b) < separation * 2 for a, b, _ in proposals):
                continue
            proposals.append((x, y, min(1., (strength - threshold) / max(1., dispersion))))
            if len(proposals) >= max(4, int(math.sqrt(len(scores)))):
                break
        return tuple(proposals)

    def cursor(self):
        p = POINT()
        if not u.GetCursorPos(ctypes.byref(p)):
            raise OSError('无法读取鼠标位置')
        return (p.x, p.y)

    def keys(self):
        return {k: bool(u.GetAsyncKeyState(v) & 0x8000) for k, v in (('l', 1), ('r', 2), ('m', 4))}

    def keyboard_activity(self):
        return any(u.GetAsyncKeyState(key) & 0x8000 for key in range(1, 256) if key not in (1, 2, 4, 5, 6))

    @staticmethod
    def resample(image):
        import numpy as np
        ih, iw = image.shape[:2]
        if ih == VIS_H and iw == VIS_W:
            sample = image[:, :, :3]
        else:
            try:
                import cv2
                method = cv2.INTER_AREA if (ih > VIS_H or iw > VIS_W) else cv2.INTER_CUBIC
                sample = cv2.resize(image[:, :, :3], (VIS_W, VIS_H), interpolation=method)
                return sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes()
            except (ImportError, OSError, RuntimeError, ValueError):
                pass
            fy = ((np.arange(VIS_H, dtype=np.float32) + .5) * (ih / VIS_H) - .5).clip(0, ih - 1)
            fx = ((np.arange(VIS_W, dtype=np.float32) + .5) * (iw / VIS_W) - .5).clip(0, iw - 1)
            ya = np.floor(fy).astype(np.intp)
            xa = np.floor(fx).astype(np.intp)
            wy = (fy - ya).clip(0., 1.)[:, None, None]
            wx = (fx - xa).clip(0., 1.)[None, :, None]
            ya = ya.clip(0, ih - 1)
            xa = xa.clip(0, iw - 1)
            yb = (ya + 1).clip(0, ih - 1)
            xb = (xa + 1).clip(0, iw - 1)
            top = image[ya[:, None], xa[None, :], :3].astype(np.float32) * (1. - wx) + image[ya[:, None], xb[None, :], :3].astype(np.float32) * wx
            bottom = image[yb[:, None], xa[None, :], :3].astype(np.float32) * (1. - wx) + image[yb[:, None], xb[None, :], :3].astype(np.float32) * wx
            sample = np.clip(top * (1. - wy) + bottom * wy, 0, 255).astype(np.uint8)
        return sample[:, :, 2].tobytes() + sample[:, :, 1].tobytes() + sample[:, :, 0].tobytes()

    def captured(self, content, backend, stamp, frame_id=None):
        self.capture_metadata.append((backend, stamp, frame_id))
        return content

    def capture(self, x, y, w, h, force_gdi=False):
        if not force_gdi and self.capture_preference == 'auto' and self.wgc is not None:
            try:
                if self.frozen_wgc is not None:
                    image, stamp, frame_id = self.frozen_wgc
                else:
                    with self.wgc_lock:
                        image, stamp, frame_id = self.wgc_frame, self.wgc_stamp, self.wgc_frame_id
                with self.wgc_lock:
                    periods = tuple(self.wgc_periods)
                wgc_latency = sorted(periods)[int((len(periods) - 1) * .95)] if periods else self.display_period
                freshness = max(2. * wgc_latency, self.last_capture_ms / 1000., self.display_period)
                if image is not None and time.monotonic() - stamp <= freshness and len(image.shape) == 3 and image.shape[2] >= 3:
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
                                x0, x1 = max(0, int(math.floor(left))), min(iw, int(math.ceil(right)))
                                y0, y1 = max(0, int(math.floor(top))), min(ih, int(math.ceil(bottom)))
                                if x1 > x0 and y1 > y0:
                                    return self.captured(self.resample(image[y0:y1, x0:x1]), 'wgc', stamp, frame_id)
            except Exception:
                self.capture_failures['wgc'] += 1
        if not force_gdi and self.capture_preference != 'gdi' and self.grabber is not None and self.grabber_errors < max(3, int(math.sqrt(max(1, self.capture_epoch + 1)))):
            try:
                cached = self.frozen_dxcam
                if cached is not None:
                    full, left, top, stamp = cached
                    if x < left or y < top or x + w > left + full.shape[1] or y + h > top + full.shape[0]:
                        raise ValueError('DXCAM 缓存区域已过期')
                    image = full[y - top:y - top + h, x - left:x - left + w]
                else:
                    image = self.grabber.grab(region=(x, y, x + w, y + h), new_frame_only=self.post_action_capture and not self.capture_metadata)
                    stamp = time.monotonic()
                    if image is not None and not self.capture_metadata and image.shape[:2] == (h, w):
                        self.frozen_dxcam = (image, x, y, stamp)
                if image is not None and len(image.shape) == 3 and image.shape[2] >= 3:
                    self.grabber_errors = 0
                    return self.captured(self.resample(image), 'dxcam', stamp)
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
        original_preference = self.capture_preference
        testing_wgc = False
        if self.capture_preference != 'auto' and self.wgc is not None:
            with self.wgc_lock:
                stamp = self.wgc_stamp
                recent = tuple(self.wgc_periods)
            period = sorted(recent)[int(.9 * (len(recent) - 1))] if recent else self.display_period
            probe_gap = max(3., 24. * max(period, self.last_capture_ms / 1000., .01))
            if stamp and capture_start - stamp < max(period * 2., self.display_period, .05) and capture_start - self.wgc_probe_at >= probe_gap:
                self.wgc_probe_at = capture_start
                self.capture_preference = 'auto'
                testing_wgc = True
        self.capture_metadata = []
        self.frozen_dxcam = None
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
            frame_budget = max(sys.float_info.epsilon, self.display_period, self.last_capture_ms / 1000.)
            capture_pressure = (self.last_capture_ms / 1000.) / frame_budget
            focus = max(base, min(1., base * (1. + complexity) / (1. + max(0., capture_pressure - .75))))
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
            self.frozen_dxcam = None
        captured_at = time.monotonic()
        modes = tuple(record[0] for record in self.capture_metadata)
        backend = modes[0] if len(modes) == 2 and modes[0] == modes[1] else 'mixed'
        if self.capture_preference == 'dxcam' and backend == 'gdi':
            self.capture_preference = 'gdi'
            self.capture_recovery = 'DXCAM 未提供可用新帧，已切换为 GDI 连续采集'
        ids = [record[2] for record in self.capture_metadata]
        self.last_frame_id = ids[0] if backend == 'wgc' and len(set(ids)) == 1 else -1
        self.last_frame_valid = backend != 'mixed' and len(result) == VIS_N and (backend != 'wgc' or self.last_frame_id >= 0)
        if backend == 'gdi' and len(self.capture_metadata) == 2:
            self.last_frame_valid = self.last_frame_valid and all(stamp >= capture_start for _, stamp, _ in self.capture_metadata)
        if backend == 'dxcam' and len(self.capture_metadata) == 2 and self.capture_metadata[0][1] != self.capture_metadata[1][1]:
            self.last_frame_valid = False
        if backend != self.last_frame_backend:
            self.capture_epoch += 1
            self.last_frame_backend = backend
        self.last_capture_stamp = min((stamp for _, stamp, _ in self.capture_metadata), default=0.)
        recent_periods = sorted(self.wgc_periods)
        measured_period = recent_periods[int((len(recent_periods) - 1) * .95)] if recent_periods else self.display_period
        if backend == 'wgc' and captured_at - self.last_capture_stamp > max(2. * measured_period, captured_at - capture_start):
            self.last_frame_valid = False
        self.last_capture_ms = (captured_at - capture_start) * 1000
        if backend in self.capture_quality:
            record = self.capture_quality[backend]
            age_ms = max(0., (captured_at - self.last_capture_stamp) * 1000.)
            penalty = age_ms if backend == 'wgc' else 0.
            sample = self.last_capture_ms + penalty
            record['samples'] += 1
            record['bad'] += int(not self.last_frame_valid)
            record['mean_ms'] = sample if record['samples'] == 1 else record['mean_ms'] * .85 + sample * .15
        if testing_wgc and backend != 'wgc':
            self.capture_preference = original_preference
        if capture_start - self.capture_selected_at >= max(1., self.display_period * 120.):
            alternatives = []
            for mode, data in self.capture_quality.items():
                if data['samples'] < 3 or mode == 'dxcam' and self.grabber is None or mode == 'wgc' and self.wgc is None:
                    continue
                failure = data['bad'] / max(1, data['samples'])
                penalty = max(self.display_period * 1000., self.last_capture_ms, 1.)
                alternatives.append((data['mean_ms'] + penalty * failure, mode))
            if len(alternatives) >= 2:
                _, choice = min(alternatives)
                new_preference = 'auto' if choice == 'wgc' else choice
                if new_preference != self.capture_preference and self.capture_quality[choice]['samples'] >= 3:
                    self.capture_preference = new_preference
                    self.capture_selected_at = capture_start
                    self.capture_recovery = '根据实测采集延迟和有效帧率选择 ' + choice.upper()
        return result

    def fresh_image(self, region, action_finished, expected_epoch, stop, action_started=None):
        with self.wgc_lock:
            recent = sorted(self.wgc_periods)
        period = recent[min(len(recent) - 1, int(len(recent) * .9))] if recent else max(self.display_period, self.last_capture_ms / 1000., sys.float_info.epsilon)
        capture_cost = self.last_capture_ms / 1000.
        recent_periods = sorted(self.wgc_periods)
        jitter = (recent_periods[-1] - recent_periods[0]) if len(recent_periods) > 1 else 0.
        budget = max(2. * period + jitter, 2. * capture_cost + period, self.display_period)
        deadline = action_finished + budget
        initial_id = self.last_frame_id
        earliest_fallback = action_finished + (self.display_period or period)
        action_started = action_finished if action_started is None else action_started
        original_backend = self.last_frame_backend
        self.capture_recovery = ''
        self.post_action_capture = True
        try:
            while not stop.is_set():
                self.safe(region, stop)
                if self.last_frame_backend == 'gdi' and time.monotonic() < earliest_fallback:
                    if stop.wait(min(.02, earliest_fallback - time.monotonic())):
                        raise InterruptedError('控制已停止')
                    continue
                captured_after = time.monotonic()
                frame = self.image(region)
                if self.capture_epoch != expected_epoch:
                    if original_backend != self.last_frame_backend:
                        if self.last_frame_backend in ('dxcam', 'gdi'):
                            self.capture_preference = self.last_frame_backend
                        self.capture_recovery = f'采集源从 {original_backend} 变为 {self.last_frame_backend}，已固定备用采集源'
                    else:
                        self.capture_recovery = '画面采集会话发生变化，正在重新同步'
                    return None
                if self.last_frame_backend == 'wgc':
                    fresh = self.last_frame_id >= 0 and self.last_frame_id != initial_id and self.last_capture_stamp >= action_started
                elif self.last_frame_backend == 'dxcam':
                    fresh = self.last_capture_stamp >= action_finished
                else:
                    fresh = captured_after >= earliest_fallback and self.last_capture_stamp >= action_finished
                if self.last_frame_valid and fresh:
                    return frame
                if time.monotonic() >= deadline:
                    if self.last_frame_backend == 'wgc':
                        self.capture_preference = 'dxcam' if self.grabber is not None and self.grabber_errors < max(3, int(math.sqrt(max(1, self.capture_epoch + 1)))) else 'gdi'
                        self.capture_recovery = f'WGC 在 {budget:.2f}s 内未更新，已改用 {self.capture_preference.upper()} 采集'
                    elif self.last_frame_backend == 'dxcam':
                        self.capture_preference = 'gdi'
                        self.capture_recovery = 'DXCAM 无法确认动作后新画面，已改用 GDI 连续采集'
                    else:
                        self.capture_recovery = f'{self.last_frame_backend} 截图未通过新鲜度校验，等待重新同步'
                    return None
                if stop.wait(min(.02, max(0., deadline - time.monotonic()))):
                    raise InterruptedError('控制已停止')
            raise InterruptedError('控制已停止')
        finally:
            self.post_action_capture = False

    def input_stop(self, stop):
        return AnyStop(stop, self.halted, self.user_override, InputLeaseStop(self))

    def safe(self, region, stop, require_pointer=True):
        if self.input_generation_guard is not None and not self.input_generation_guard(self.input_generation):
            raise InterruptedError('本轮 AI 控制许可已被真实输入撤销')
        if self.user_override.is_set():
            raise InterruptedError('检测到真实输入，暂停 AI 鼠标控制')
        if self.keyboard_guard is not None and not self.keyboard_guard.is_set():
            raise RuntimeError('输入急停监控暂不可用，禁止发送鼠标指令')
        if self.human_guard is not None and not self.human_guard():
            raise InterruptedError('用户已恢复操作，禁止发送鼠标指令')
        if stop.is_set() or self.halted.is_set():
            raise InterruptedError('键盘急停')
        if self.keyboard_activity():
            self.halted.set()
            raise InterruptedError('检测到键盘输入')
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
                send_cursor(x + w // 2, y + h // 2, self.input_stop(stop))
                ensure_cursor(x + w // 2, y + h // 2, .2, self.input_stop(stop))
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
            self.release_uncertain = True
            send_mouse(flags[name][0 if press else 1], stop=self.input_stop(stop) if stop is not None else self.input_stop(self.halted))
            self.down[name] = press
            self.release_uncertain = False
            if press:
                self.hold_since[name] = time.monotonic()
                self.hold_last_motion[name] = self.hold_since[name]
            else:
                self.hold_last_motion.pop(name, None)
                started = self.hold_since.pop(name, None)
                if started is not None:
                    self.hold_history.append(max(0., time.monotonic() - started))
            return True

    def quick_release(self):
        with self.io_lock:
            failure = None
            uncertain = self.release_uncertain
            for name, flag in (('l', 4), ('r', 16), ('m', 64)):
                if not self.down[name] and not uncertain:
                    continue
                try:
                    send_mouse(flag)
                    self.down[name] = False
                    self.hold_last_motion.pop(name, None)
                    started = self.hold_since.pop(name, None)
                    if started is not None:
                        self.hold_history.append(max(0., time.monotonic() - started))
                except OSError as error:
                    failure = error
            self.release_uncertain = failure is not None
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
            movement_limit = math.hypot(max(1., w / VIS_W), max(1., h / VIS_H))
            if self.last_ai_cursor is not None and math.hypot(px - self.last_ai_cursor[0], py - self.last_ai_cursor[1]) > movement_limit:
                self.velocity = (0., 0.)
                self.last_ai_cursor = (px, py)
            vx, vy, speed, l, r, m, wheel, duration = ctrl
            dt = max(sys.float_info.epsilon, float(dt))
            speed_limit = speed_reference(region, dt)
            magnitude = max(.0, min(1., speed)) * speed_limit * self.motion_scale
            norm = math.hypot(vx, vy)
            ux, uy = ((vx / norm, vy / norm) if norm > .001 else (0., 0.))
            desired = (ux * magnitude, uy * magnitude)
            smooth = dt / (dt + max(dt / max(1., math.sqrt(max(1, w * h))), self.last_capture_ms / 1000.))
            velocity = (self.velocity[0] * (1 - smooth) + desired[0] * smooth, self.velocity[1] * (1 - smooth) + desired[1] * smooth)
            if not magnitude:
                velocity = (0., 0.)
            clearance_x = max(1, math.ceil(w / VIS_W))
            clearance_y = max(1, math.ceil(h / VIS_H))
            nx = max(x + clearance_x, min(x + w - 1 - clearance_x, round(px + velocity[0] * dt)))
            ny = max(y + clearance_y, min(y + h - 1 - clearance_y, round(py + velocity[1] * dt)))
            self.safe(region, stop)
            if stop.is_set():
                raise InterruptedError('键盘急停')
            if (nx, ny) != (px, py):
                send_cursor(nx, ny, self.input_stop(stop))
                ensure_cursor(nx, ny, max(.02, min(.1, dt + self.last_capture_ms / 1000.)), self.input_stop(stop))
            self.safe(region, stop)
            ex, ey = self.cursor()
            dx, dy = ex - px, ey - py
            self.last_ai_cursor = (ex, ey)
            self.velocity = (dx / dt, dy / dt)
            expected_movement = math.hypot(nx - px, ny - py)
            observed_movement = math.hypot(dx, dy)
            if expected_movement > 1. and observed_movement > 0. and not stop.is_set():
                correction = max(.5, min(2., expected_movement / observed_movement))
                self.motion_scale = max(.5, min(2., self.motion_scale * .9 + correction * .1))
            switches = []
            blocked = False
            now = time.monotonic()
            observed_holds = sorted(self.hold_history)
            median_hold = observed_holds[len(observed_holds) // 2] if observed_holds else 0.
            hold_limit = max(u.GetDoubleClickTime() / 1000., median_hold + math.sqrt(max(0., sum((v - median_hold) ** 2 for v in observed_holds) / len(observed_holds))) if observed_holds else 0., dt + self.last_capture_ms / 1000.)
            if dx or dy:
                for name in self.hold_since:
                    if self.down.get(name):
                        self.hold_last_motion[name] = now
            expired = set()
            for name, started in list(self.hold_since.items()):
                last_activity = self.hold_last_motion.get(name, started)
                if self.down.get(name) and now - last_activity > hold_limit:
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
            if wheel:
                period = self.display_period or max(dt, self.last_capture_ms / 1000., time.get_clock_info('monotonic').resolution)
                self.scroll_credit = max(-1., min(1., self.scroll_credit + wheel * dt / period))
                if abs(self.scroll_credit) >= 1.:
                    self.safe(region, stop)
                    delta = 120 if self.scroll_credit > 0. else -120
                    send_mouse(0x0800, delta, stop=self.input_stop(stop))
                    self.scroll_credit -= math.copysign(1., self.scroll_credit)
            action = observed_action(dx, dy, dt, speed_limit, wheel, delta, switches)
            real_speed = min(1., math.hypot(dx, dy) / (dt * speed_limit))
            distance = math.hypot(dx, dy)
            executed = [dx / distance if distance else 0., dy / distance if distance else 0., real_speed, 0., 0., 0., math.copysign(abs(wheel), delta) if delta else 0., max(0., min(1., dt / max(sys.float_info.epsilon, u.GetDoubleClickTime() / 1000.)))]
            for switch in switches:
                executed[{'l': 3, 'r': 4, 'm': 5}[switch[0]]] = 1. if switch[1] == '+' else -1.
            changed = bool(dx or dy or switches or delta)
            pending_scroll = bool(wheel and not delta)
            requested = bool(magnitude or delta or blocked or switches)
            intended_distance = magnitude * dt
            motion_fidelity = max(0., 1. - abs(distance - intended_distance) / max(1., intended_distance)) if intended_distance else 1.
            button_expected = [(name, target) for name, target in zip(('l', 'r', 'm'), (l, r, m)) if abs(target) > .5]
            button_fidelity = sum(self.down[name] == (target > .5) for name, target in button_expected) / len(button_expected) if button_expected else 1.
            efficacy = max(0., min(1., motion_fidelity * button_fidelity))
            return {'action': action, 'ctrl': tuple(executed), 'scroll': delta, 'switches': tuple(switches), 'blocked': blocked or (requested and not changed), 'pending_scroll': pending_scroll, 'changed': changed, 'moved': distance, 'efficacy': efficacy}

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
                if not name or any(x in name.lower() for x in ('basic display', 'remote display', 'mirror driver')):
                    continue
                if 'ven_10de' in item.DeviceID.lower() and 'nvidia' not in name.lower():
                    name = 'NVIDIA ' + name
                if name not in names:
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
        if not passed:
            detail = [line for line in lines if line.strip()]
            try:
                save_json(Path(folder) / '.probe_diagnostics.gz', {'when': time.time(), 'backend': backend, 'runtime': str(runtime) if runtime else 'system', 'reason': detail[-1][:300] if detail else '进程未能完成 GPU 检测'})
            except (OSError, ValueError):
                pass
            if report is not None:
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


def installation_due(folder, name):
    path = Path(folder) / ('.retry_' + name + '.gz')
    state = read_json(path, {})
    if not isinstance(state, dict):
        return True
    try:
        attempts = max(0, int(state.get('failures', 0)))
        cost = max(1., float(state.get('duration', 1.)))
        failed_at = float(state.get('time', 0.))
        if not math.isfinite(cost) or not math.isfinite(failed_at):
            return True
        retry = min(900., max(15., math.ldexp(cost, min(attempts, 8))))
        return time.time() >= failed_at + retry
    except (ValueError, TypeError, OverflowError):
        return True


def installation_result(folder, name, started, success):
    path = Path(folder) / ('.retry_' + name + '.gz')
    if success:
        try:
            path.unlink(missing_ok=True)
        except OSError:
            pass
        return
    previous = read_json(path, {})
    try:
        failures = max(0, int(previous.get('failures', 0))) if isinstance(previous, dict) else 0
    except (ValueError, TypeError, OverflowError):
        failures = 0
    save_json(path, {'failures': min(32, failures + 1), 'duration': max(1., time.monotonic() - started), 'time': time.time()})


def python_runtime_id():
    identity = (sys.implementation.cache_tag, sysconfig.get_config_var('SOABI'),
                sysconfig.get_config_var('EXT_SUFFIX'), struct.calcsize('P') * 8,
                sys.version_info[:3], sys.executable)
    digest = hashlib.blake2s(repr(identity[:-1]).encode('utf-8'), digest_size=6).hexdigest()
    return 'py' + str(sys.version_info.major) + str(sys.version_info.minor) + '_' + digest


def managed_runtime(folder, backend):
    return Path(folder) / ('.runtime_' + backend + '_' + python_runtime_id())


def runtime_versions(path):
    versions = {}
    for kind in ('torch', 'torch_directml', 'windows_capture'):
        found = sorted(Path(path).glob(kind.replace('_', '[-_]') + '-*.dist-info'))
        if not found:
            found = sorted(Path(path).glob(kind + '-*.dist-info'))
        if found:
            versions[kind] = found[-1].name.rsplit('.dist-info', 1)[0]
    return versions


def runtime_valid(path, backend):
    path = Path(path)
    if not path.is_dir():
        return False
    expected = 'torch_directml' if backend == 'directml' else ('windows_capture' if backend == 'capture' else 'torch')
    if not (path / expected).exists():
        return False
    record = read_json(path / '.mouseai_runtime.gz', {})
    return (isinstance(record, dict) and record.get('python') == python_runtime_id()
            and expected in runtime_versions(path)
            and record.get('versions') == runtime_versions(path)
            and record.get('backend') == backend)


def mark_runtime(path, backend):
    save_json(Path(path) / '.mouseai_runtime.gz', {
        'python': python_runtime_id(), 'backend': backend,
        'versions': runtime_versions(path), 'created': time.time()})


def purge_stale_installers(folder):
    now = time.time()
    for path in Path(folder).glob('.install_*'):
        try:
            if path.is_dir() and now - path.stat().st_mtime > 86400:
                shutil.rmtree(path, ignore_errors=True)
        except OSError:
            pass
    for path in Path(folder).glob('.installation_*.log'):
        try:
            if now - path.stat().st_mtime > 30 * 86400:
                path.unlink(missing_ok=True)
        except OSError:
            pass


def install_package(folder, args, report, cancel, backend):
    if cancel.is_set():
        return False
    folder.mkdir(parents=True, exist_ok=True)
    purge_stale_installers(folder)
    target = managed_runtime(folder, backend)
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
            while proc.poll() is None:
                if cancel.is_set():
                    stop_process_tree(proc)
                    report(backend + ' 配置已取消，保留之前的计算组件')
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
        mark_runtime(packages, backend)
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


def nvidia_compute_capabilities():
    if os.name != 'nt':
        return []
    binaries = ('nvidia-smi', str(Path(os.environ.get('SystemRoot', 'C:/Windows')) / 'System32' / 'nvidia-smi.exe'),
                str(Path(os.environ.get('ProgramFiles', 'C:/Program Files')) / 'NVIDIA Corporation' / 'NVSMI' / 'nvidia-smi.exe'))
    for binary in binaries:
        try:
            check = subprocess.run([binary, '--query-gpu=name,compute_cap', '--format=csv,noheader,nounits'], capture_output=True, text=True, timeout=7, creationflags=subprocess.CREATE_NO_WINDOW)
            if check.returncode == 0 and check.stdout.strip():
                return [item.strip() for item in check.stdout.splitlines() if item.strip()]
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
    abi = tag + ('t' if sysconfig.get_config_var('Py_GIL_DISABLED') else '')
    wheel_tag = tag + '-' + abi
    driver_key = list(driver) if driver is not None else None
    def compatible(wheel):
        digits = wheel[2:]
        major = int(digits[:-2]) if len(digits) == 4 else int(digits[:-1])
        minor = int(digits[-2:]) if len(digits) == 4 else int(digits[-1])
        return driver is None or (major, minor) <= driver
    if cache is not None:
        saved = read_json(cache, {})
        if isinstance(saved, dict) and saved.get('driver') == driver_key and saved.get('python') == wheel_tag and isinstance(saved.get('when'), (int, float)) and time.time() - saved['when'] < 86400:
            values = saved.get('wheels')
            if isinstance(values, list) and values and all(isinstance(v, str) and re.fullmatch(r'cu\d{3,4}', v) for v in values):
                return [wheel for wheel in values if compatible(wheel)]
    cached = read_json(cache, {}) if cache is not None else {}
    verified_cache = cached.get('wheels', []) if isinstance(cached, dict) and cached.get('python') == wheel_tag else []
    verified_cache = [wheel for wheel in verified_cache if isinstance(wheel, str) and re.fullmatch(r'cu\d{3,4}', wheel)]
    versions = []
    try:
        with urllib.request.urlopen('https://download.pytorch.org/whl/', timeout=7) as response:
            listing = response.read(1000000).decode('utf-8', errors='replace')
        versions = ['cu' + value for value in set(re.findall(r'(?i)href=["\'][^"\']*cu(\d{3,4})/?["\']', listing))]
    except (OSError, ValueError, TimeoutError):
        versions = verified_cache
    versions = sorted(set(wheel for wheel in versions if compatible(wheel)), key=lambda w: int(w[2:]), reverse=True)
    supported = []
    unreachable = False
    for wheel in versions:
        if cancel is not None and cancel.is_set():
            break
        try:
            with urllib.request.urlopen('https://download.pytorch.org/whl/' + wheel + '/torch/', timeout=6) as response:
                for line in response:
                    if cancel is not None and cancel.is_set():
                        break
                    candidate = html.unescape(urllib.parse.unquote(line.decode('utf-8', errors='replace').lower()))
                    if re.search(r'torch-[^<>"\s/]+-' + tag + r'-' + abi + r'-win_amd64\.whl', candidate):
                        supported.append(wheel)
                        break
        except urllib.error.HTTPError as error:
            if error.code != 404:
                unreachable = True
                break
        except (OSError, ValueError, TimeoutError):
            unreachable = True
            break
    if unreachable:
        supported = sorted(set(supported) | {wheel for wheel in verified_cache if compatible(wheel)}, key=lambda w: int(w[2:]), reverse=True)
    if cache is not None and supported and not unreachable:
        try:
            save_json(cache, {'when': time.time(), 'python': wheel_tag, 'driver': driver_key, 'wheels': supported})
        except (OSError, ValueError, TypeError):
            pass
    return supported


def gpu_failure_category(detail):
    message = str(detail).lower()
    if any(part in message for part in ('out of memory', 'cuda error: out of memory', 'not enough memory', '显存')):
        return '显存不足'
    if any(part in message for part in ('no kernel image', 'unsupported gpu', 'sm_', 'invalid device function')):
        return '显卡架构与计算包不兼容'
    if any(part in message for part in ('driver', 'dll load failed', 'nvcuda', '驱动')):
        return '显卡驱动或设备初始化失败'
    if any(part in message for part in ('no module named', 'module not found', 'importerror', 'winerror 126', '动态链接')):
        return '运行时依赖不完整'
    if any(part in message for part in ('timed out', 'timeout', 'connection', '网络')):
        return '下载或验证通信失败'
    return 'GPU 实际运算验证失败'


def load_brain(folder, report, cancel, runtime_folder=None, gpu_only=False, cuda_only=False):
    folder.mkdir(parents=True, exist_ok=True)
    runtime_folder = Path(runtime_folder) if runtime_folder is not None else folder
    runtime_folder.mkdir(parents=True, exist_ok=True)
    cache = runtime_folder / '.cache'
    cache.mkdir(parents=True, exist_ok=True)
    for key in ('TEMP', 'TMP', 'TMPDIR', 'XDG_CACHE_HOME', 'TORCH_HOME', 'CUDA_CACHE_PATH', 'TORCHINDUCTOR_CACHE_DIR', 'TRITON_CACHE_DIR', 'PIP_CACHE_DIR', 'NUMBA_CACHE_DIR'):
        os.environ[key] = str(cache)
    gpus = detect_gpu()
    nvidia = any('nvidia' in name.lower() for name in gpus)
    stable_drivers = [line.rsplit(',', 1)[0].strip() for line in nvidia_driver_info()] if os.name == 'nt' else []
    if gpus:
        report('识别的图形设备：' + '、'.join(gpus[:4]))
    if os.name == 'nt' and not nvidia and (nvidia_driver_info() or cuda_driver_version()):
        nvidia = True
        gpus.append('NVIDIA GPU')
    if nvidia and os.environ.get('CUDA_VISIBLE_DEVICES', 'visible').strip().lower() in ('', '-1', 'none', 'void'):
        report('检测到 CUDA 设备被环境变量遮蔽；将在独立计算进程中自动尝试恢复可见性')
    device_fingerprint = hashlib.blake2s(('|'.join(gpus) + repr(stable_drivers) + sys.version + sys.executable).encode('utf-8', errors='replace'), digest_size=10).hexdigest() if os.name == 'nt' else ''
    cuda_runtimes = sorted((path for path in runtime_folder.glob('.runtime_cuda_cu*')
                            if path.name.endswith('_' + python_runtime_id())
                            and runtime_valid(path, path.name[len('.runtime_'):].rsplit('_' + python_runtime_id(), 1)[0])), reverse=True)
    directml_runtime = managed_runtime(runtime_folder, 'directml')
    cpu_runtime = managed_runtime(runtime_folder, 'cpu')
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
        def launch(runtime, backend, force=False):
            key = (str(runtime) if runtime is not None else '', backend)
            if (key in tried and not force) or cancel.is_set():
                return None
            tried.add(key)
            retry_key = 'verify_' + backend + '_' + hashlib.blake2s((device_fingerprint + str(runtime) + python_runtime_id()).encode(), digest_size=8).hexdigest()
            if backend in ('cuda', 'directml') and not force and not installation_due(runtime_folder, retry_key):
                return None
            started = time.monotonic()
            try:
                ready = RemoteBrain(folder, runtime, backend, cancel)
                if backend in ('cuda', 'directml'):
                    installation_result(runtime_folder, retry_key, started, True)
                if backend in ('cuda', 'directml'):
                    try:
                        save_json(runtime_folder / '.backend_preference.gz', {'backend': backend, 'runtime': runtime.name if runtime is not None else '', 'fingerprint': device_fingerprint, 'verified_at': time.time()})
                    except (OSError, ValueError):
                        pass
                return ready
            except Exception as error:
                detail = backend + ' (' + (runtime.name if runtime else '系统运行时') + ') [' + gpu_failure_category(error) + ']：' + str(error)[:180]
                failures.append(detail)
                if not cancel.is_set():
                    if backend in ('cuda', 'directml'):
                        installation_result(runtime_folder, retry_key, started, False)
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
            architectures = nvidia_compute_capabilities()
            if architectures:
                report('CUDA 计算架构：' + '；'.join(architectures[:2])[:180] + '；将以模型前向/反向计算验证实际可用性')
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
            wheels = available_cuda_wheels(driver, cancel, runtime_folder) if driver is not None else []
            if driver is not None:
                report('驱动接口已确认 CUDA ' + '.'.join(map(str, driver)) + '；正在配置匹配 PyTorch，并测试真实模型计算')
            else:
                report('已识别 NVIDIA 设备，但 CUDA 驱动接口尚未就绪；跳过不兼容的 CUDA 下载并尝试 DirectML')
            if not wheels and driver is not None:
                report('未发现适配当前 Python 和驱动的 Windows CUDA 安装包，或下载源不可访问；随后尝试 DirectML')
            for wheel in wheels:
                if cancel.is_set():
                    break
                runtime = managed_runtime(runtime_folder, 'cuda_' + wheel)
                if runtime_valid(runtime, 'cuda_' + wheel):
                    ready = launch(runtime, 'cuda')
                    if ready is not None:
                        return ready
                    report('已安装的 CUDA 运行环境未通过验证，将自动尝试修复')
                retry_name = 'cuda_' + wheel + '_' + device_fingerprint + '_' + python_runtime_id()
                if not installation_due(runtime_folder, retry_name):
                    continue
                install_started = time.monotonic()
                installed = install_package(runtime_folder, ['--only-binary=:all:', '--index-url', 'https://download.pytorch.org/whl/' + wheel, 'torch'], report, cancel, 'cuda_' + wheel)
                ready = launch(runtime, 'cuda', force=True) if installed else None
                if not cancel.is_set():
                    try:
                        installation_result(runtime_folder, retry_name, install_started, ready is not None)
                    except (OSError, ValueError, TypeError):
                        pass
                if ready is not None:
                    return ready
        if cuda_only:
            if failures:
                report('CUDA 自动升级暂不可用：' + failures[-1][:130] + '；保留正在运行的 DirectML')
            return None
        directml_candidates = ([directml_runtime, None] if directml_runtime.exists() else [None]) if gpus or directml_runtime.exists() else []
        for runtime in directml_candidates:
            ready = launch(runtime, 'directml')
            if ready is not None:
                return ready
        if gpus and not cancel.is_set() and (not runtime_valid(directml_runtime, 'directml') or (str(directml_runtime), 'directml') in tried) and installation_due(runtime_folder, 'directml_' + device_fingerprint + python_runtime_id()):
            install_started = time.monotonic()
            installed = install_package(runtime_folder, ['torch-directml'], report, cancel, 'directml')
            ready = launch(directml_runtime, 'directml', force=True) if installed else None
            if not cancel.is_set():
                try:
                    installation_result(runtime_folder, 'directml_' + device_fingerprint + python_runtime_id(), install_started, ready is not None)
                except (OSError, ValueError, TypeError):
                    pass
            if ready is not None:
                return ready
    if gpus and not cancel.is_set():
        try:
            save_json(runtime_folder / '.hardware_diagnostics.gz', {'when': time.time(), 'devices': gpus, 'failures': failures if os.name == 'nt' else [], 'python': sys.version, 'cuda_driver': cuda_driver_version(), 'compute_capability': nvidia_compute_capabilities(), 'fingerprint': device_fingerprint})
        except (OSError, ValueError):
            pass
        report('显卡已识别；CUDA/DirectML 暂未通过前向与反向计算验证，已保存诊断并继续使用基础引擎')
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
    memory = available_memory()
    can_install = not memory or memory > VIS_N * REPLAY_LIMIT * 3
    try:
        if can_install and not cancel.is_set() and installation_due(runtime_folder, 'cpu_' + python_runtime_id()):
            started = time.monotonic()
            installed = install_package(runtime_folder, ['--only-binary=:all:', '--index-url', 'https://download.pytorch.org/whl/cpu', 'torch'], report, cancel, 'cpu')
            if installed:
                try:
                    ready = RemoteBrain(folder, cpu_runtime, 'cpu', cancel)
                    installation_result(runtime_folder, 'cpu_' + python_runtime_id(), started, True)
                    return ready
                except (OSError, RuntimeError, ValueError) as error:
                    report('CPU 深度学习后端验证失败：' + str(error)[:120])
                    installed = False
            if not cancel.is_set():
                installation_result(runtime_folder, 'cpu_' + python_runtime_id(), started, False)
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
    runtime = managed_runtime(folder, 'capture')
    if runtime_valid(runtime, 'capture'):
        if str(runtime) not in sys.path:
            sys.path.insert(0, str(runtime))
        importlib.invalidate_caches()
        try:
            importlib.import_module('windows_capture')
            return
        except (ImportError, OSError, RuntimeError):
            pass
    if not installation_due(folder, 'capture_' + python_runtime_id()):
        return
    started = time.monotonic()
    installed = False
    try:
        if install_package(folder, ['windows-capture'], report, cancel, 'capture'):
            if str(runtime) not in sys.path:
                sys.path.insert(0, str(runtime))
            importlib.invalidate_caches()
            importlib.import_module('windows_capture')
            installed = True
    except (OSError, ImportError, RuntimeError, ValueError):
        pass
    if not cancel.is_set():
        try:
            installation_result(folder, 'capture_' + python_runtime_id(), started, installed)
        except (OSError, ValueError, TypeError):
            pass


class MouseAIApp:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title('窗口鼠标 AI')
        self.root.configure(bg='#10131a')
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        work_width, work_height = screen_width, screen_height
        if os.name == 'nt':
            try:
                usable = RECT()
                system = ctypes.WinDLL('user32', use_last_error=True)
                system.SystemParametersInfoW.argtypes = (wintypes.UINT, wintypes.UINT, ctypes.c_void_p, wintypes.UINT)
                if system.SystemParametersInfoW(0x30, 0, ctypes.byref(usable), 0):
                    work_width = max(320, usable.right - usable.left)
                    work_height = max(320, usable.bottom - usable.top)
            except (OSError, ValueError, AttributeError):
                pass
        self.root.geometry(f'{max(300, min(980, work_width - 48))}x{max(300, min(850, work_height - 35))}')
        self.root.minsize(min(500, work_width), min(360, work_height))
        home = Path.home()
        self.folder = (home / 'Documents' / 'MouseAI') if (home / 'Documents').exists() else (home / 'MouseAI')
        self.folder_origin_default = True
        self.hardware_probe_thread = None
        self.control_stop = threading.Event()
        self.observer_stop = threading.Event()
        self.human_lock = threading.RLock()
        self.user_override = threading.Event()
        self.user_override.set()
        self.takeover_permission = threading.Event()
        self.takeover_window = None
        self.takeover_check = tk.BooleanVar(value=False)
        self.explore_check = tk.BooleanVar(value=False)
        self.explore_permission = threading.Event()
        self.human_last_input = time.monotonic()
        self.human_gaps = deque(maxlen=256)
        self.human_events = deque(maxlen=4096)
        self.human_event_id = 0
        self.observed_count = 0
        self.session_hwnd = None
        self.pending_folder = None
        self.next_observer_retry = 0.
        self.handoff_pending = False
        self.control_state = '空闲'
        self.online_stop = threading.Event()
        self.online_worker = None
        self.online_error = None
        self.active_io = None
        self.release_worker = None
        self.release_signal = threading.Event()
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
        self.start_queued = None
        self.control_worker = None
        self.control_heartbeat = 0.
        self.watchdog_limit = 1.
        self.control_interval = 0.
        self.close_started = 0.
        self.saver = None
        self.capture_worker = None
        self.acceleration_lock = threading.Lock()
        self.engine_init_lock = threading.RLock()
        self.initializer = None
        self.selected_key = ''
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
        self.storage_checked_at = 0.
        self.control_history = deque(maxlen=max(4, int(math.sqrt(REPLAY_LIMIT))))
        self.next_backend_retry = 0.
        self.acceleration_failures = 0
        self.acceleration_retry_signature = None
        self.nvidia_present = None
        self.backend_faults = {}
        self.brain = None
        self.brain_folder = None
        self.goal_atlas = None
        self.mode = 'idle'
        self.task_failed = False
        self.task_outcome = None
        self.keyboard_stopped_control = threading.Event()
        self.switching_folder = False
        self.message = queue.Queue()
        self.fast_messages = {}
        self.fast_messages_lock = threading.Lock()
        self.listing = {}
        self.iterations = 0
        self.backend = tk.StringVar(value='尚未启动 · 正在识别 GPU / CUDA')
        self.folder_text = tk.StringVar(value=str(self.folder))
        self.status = tk.StringVar(value='选择目标窗口后静默学习；勾选无人值守授权后，空闲时才允许自主控制')
        self.phase = tk.StringVar(value='空闲')
        self.progress_value = tk.DoubleVar(value=0.)
        self.progress_text = tk.StringVar(value='准备状态 · 0%')
        self.issue = tk.StringVar(value='无')
        self.statistics = tk.StringVar(value='经验 0 条 · 实际操作 0 次 · 可控进展待观测（非任务成功率）')
        self.learning_summary = tk.StringVar(value='学习：暂无经验 · 进展尚待观测')
        self.capture_text = tk.StringVar(value=f'视觉输入 {VIS_W}×{VIS_H} 双视野 · 客户区与局部视野自动取样 · 总像素 {PIXELS * 2:,}')
        self.goal_text = tk.StringVar(value='等待观察 · 尚未建立状态目标')
        self.safety_text = tk.StringVar(value='键盘急停监控正在启动')
        self.fps_text = tk.StringVar(value='控制 FPS：尚未测量')
        self.gpu_state = tk.StringVar(value='GPU：正在识别硬件 · 尚未验证训练')
        self.storage_state = tk.StringVar(value='存储：等待选择数据目录')
        self.control_details = tk.StringVar(value='鼠标未控制 · 左键释放 · 右键释放 · 中键释放 · 滚轮停止')
        self.combo_var = tk.StringVar()
        self.environment_code = (0., 0.)
        self.data_folder = self.folder
        self.audit_sum = 0.
        self.audit_samples = 0
        self.preview_at = 0.
        self.preview_photos = []
        self.preview_canvas = None
        self.preview_inner = None
        self.preview_frame = None
        self.build()
        self.root.protocol('WM_DELETE_WINDOW', self.close)
        self.root.after(90, self.pump)
        self.root.after(300, self.report_storage)
        self.refresh_after = None
        self.refresh_after = self.root.after(400, self.refresh)
        self.key_thread = threading.Thread(target=self.keyboard_supervisor, daemon=True)
        self.key_thread.start()
        self.safety_thread = threading.Thread(target=self.safety_sentinel, daemon=True)
        self.safety_thread.start()

    def build(self):
        compact = self.root.winfo_screenheight() < 920
        sty = ttk.Style(self.root)
        try:
            sty.theme_use('clam')
        except tk.TclError:
            pass
        sty.configure('AI.TCombobox', font=('Microsoft YaHei UI', 10), padding=4 if compact else 6)
        title = tk.Label(self.root, text='窗口鼠标 AI', bg='#10131a', fg='#f2f5fa', font=('Microsoft YaHei UI', 16 if compact else 20, 'bold'))
        title.pack(anchor='w', padx=16, pady=(7 if compact else 12, 3))
        selector = tk.Frame(self.root, bg='#10131a')
        selector.pack(fill='x', padx=16)
        selection = tk.Frame(selector, bg='#10131a')
        selection.pack(fill='x')
        tk.Label(selection, text='目标窗口', bg='#10131a', fg='#d9e0ea', font=('Microsoft YaHei UI', 9)).pack(side='left', padx=(0, 7))
        self.combo = ttk.Combobox(selection, textvariable=self.combo_var, state='readonly', style='AI.TCombobox', font=('Microsoft YaHei UI', 9))
        self.combo.pack(side='left', fill='x', expand=True)
        self.combo.bind('<<ComboboxSelected>>', self.preload_selected)
        tk.Button(selection, text='刷新', command=self.refresh, bg='#303949', fg='white', relief='flat', cursor='hand2', font=('Microsoft YaHei UI', 9), padx=10, pady=4).pack(side='left', padx=(7, 0))
        tk.Label(self.root, text='用户操作时仅观察学习；授权后且目标窗口位于前台时，空闲可自主使用鼠标。真实输入立即中断。', bg='#10131a', fg='#9de1d5', anchor='w', justify='left', wraplength=max(280, self.root.winfo_screenwidth() - 80), font=('Microsoft YaHei UI', 9)).pack(fill='x', padx=16, pady=(5, 2))
        tk.Checkbutton(self.root, text='允许 AI 在所选窗口无人值守时自主使用鼠标（初始关闭）', variable=self.takeover_check,
                       command=self.change_takeover_permission, bg='#10131a', fg='#f3d9a4', selectcolor='#303949',
                       activebackground='#10131a', activeforeground='#f3d9a4', anchor='w', font=('Microsoft YaHei UI', 9, 'bold')).pack(fill='x', padx=16, pady=(0, 2))
        tk.Checkbutton(self.root, text='允许探索性点击标准控件及滚动（可能改变窗口内容，默认关闭）', variable=self.explore_check,
                       command=self.change_explore_permission, bg='#10131a', fg='#e3c6ae', selectcolor='#303949',
                       activebackground='#10131a', activeforeground='#e3c6ae', anchor='w', font=('Microsoft YaHei UI', 9)).pack(fill='x', padx=16, pady=(0, 5))
        lower = tk.Frame(self.root, bg='#10131a')
        lower.pack(side='bottom', fill='x', padx=16, pady=(3, 5))
        tk.Label(lower, text='任意真实键盘或鼠标操作都能立即打断 AI；关闭窗口即可退出', bg='#10131a', fg='#ffbb85', anchor='w', font=('Microsoft YaHei UI', 9, 'bold')).pack(fill='x', pady=(0, 3))
        footer = tk.Frame(lower, bg='#10131a')
        footer.pack(fill='x')
        self.folder_button = tk.Button(footer, text='选择数据文件夹', command=self.choose_folder, bg='#303949', fg='#f5f7fa', relief='flat', padx=9, pady=4, cursor='hand2')
        self.folder_button.pack(side='left')
        self.folder_label = tk.Label(footer, textvariable=self.folder_text, bg='#10131a', fg='#8793a7', anchor='w', font=('Microsoft YaHei UI', 9))
        self.folder_label.pack(side='left', fill='x', expand=True, padx=(8, 0))
        dashboard = tk.Frame(self.root, bg='#202631', padx=10, pady=7)
        dashboard.pack(fill='x', padx=15, pady=(0, 5))
        heading = tk.Frame(dashboard, bg='#202631')
        heading.pack(fill='x')
        tk.Label(heading, text='当前阶段', bg='#202631', fg='#9aaac0').pack(side='left')
        tk.Label(heading, textvariable=self.phase, bg='#202631', fg='#69cfbd', font=('Microsoft YaHei UI', 10, 'bold')).pack(side='left', padx=(8, 12))
        tk.Label(heading, textvariable=self.fps_text, bg='#202631', fg='#69cfbd', font=('Microsoft YaHei UI', 10, 'bold')).pack(side='left')
        tk.Label(dashboard, textvariable=self.backend, bg='#202631', fg='#9de1d5', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.gpu_state, bg='#202631', fg='#9de1d5', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.capture_text, bg='#202631', fg='#b0c0d4', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.storage_state, bg='#202631', fg='#b0c0d4', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.learning_summary, bg='#202631', fg='#e0e8f2', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.safety_text, bg='#202631', fg='#ffbb85', anchor='w').pack(fill='x')
        tk.Label(dashboard, textvariable=self.issue, bg='#202631', fg='#ffbb85', anchor='w', justify='left').pack(fill='x')
        tk.Label(dashboard, textvariable=self.status, bg='#202631', fg='#e0e8f2', anchor='w', justify='left', wraplength=max(250, self.root.winfo_screenwidth() - 90)).pack(fill='x')
        progress_row = tk.Frame(dashboard, bg='#202631')
        progress_row.pack(fill='x', pady=(3, 1))
        tk.Label(progress_row, text='当前任务进度', bg='#202631', fg='#9aaac0').pack(side='left')
        tk.Label(progress_row, textvariable=self.progress_text, bg='#202631', fg='#69cfbd').pack(side='right')
        sty.configure('AI.Horizontal.TProgressbar', troughcolor='#10131a', background='#18ad65', borderwidth=0, thickness=9)
        self.progress_bar = ttk.Progressbar(dashboard, variable=self.progress_value, maximum=100, mode='determinate', style='AI.Horizontal.TProgressbar')
        self.progress_bar.pack(fill='x')
        def resize_fixed(event):
            for widget in dashboard.winfo_children():
                if isinstance(widget, tk.Label):
                    widget.configure(wraplength=max(180, event.width - 24))
        dashboard.bind('<Configure>', resize_fixed)
        viewport = tk.Frame(self.root, bg='#10131a')
        viewport.pack(fill='both', expand=True, padx=(15, 7), pady=(0, 2))
        self.preview_canvas = tk.Canvas(viewport, bg='#202631', highlightthickness=0, borderwidth=0, relief='flat')
        scrollbar = ttk.Scrollbar(viewport, orient='vertical', command=self.preview_canvas.yview)
        self.preview_canvas.configure(yscrollcommand=scrollbar.set)
        self.preview_canvas.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        panel = tk.Frame(self.preview_canvas, bg='#202631', padx=10, pady=6)
        self.preview_inner = panel
        canvas_id = self.preview_canvas.create_window((0, 0), window=panel, anchor='nw')
        def layout_panel(event=None):
            if self.preview_canvas is None:
                return
            self.preview_canvas.itemconfigure(canvas_id, width=max(1, self.preview_canvas.winfo_width()))
            self.preview_canvas.configure(scrollregion=self.preview_canvas.bbox('all'))
        panel.bind('<Configure>', layout_panel)
        self.preview_canvas.bind('<Configure>', layout_panel)
        def wheel(event):
            canvas = self.preview_canvas
            if canvas is not None and panel.winfo_reqheight() > canvas.winfo_height():
                canvas.yview_scroll(-int(math.copysign(max(1, abs(event.delta) // 120), event.delta)), 'units')
        def bind_scroll(widget):
            widget.bind('<MouseWheel>', wheel, add='+')
            for child in widget.winfo_children():
                bind_scroll(child)
        previews = tk.Frame(panel, bg='#202631')
        previews.pack(fill='x', pady=(4, 2))
        self.preview_frame = previews
        self.preview_labels = []
        for name in ('全窗口概览', '鼠标附近细节'):
            item = tk.Frame(previews, bg='#202631')
            item.pack(side='left', expand=True, fill='x')
            tk.Label(item, text=name, bg='#202631', fg='#9aaac0', font=('Microsoft YaHei UI', 9)).pack(anchor='w')
            visual = tk.Label(item, text='等待首帧', bg='#141923', fg='#74849b', width=18, height=2 if compact else 5)
            visual.pack(anchor='w', fill='x', padx=(0, 5))
            visual.bind('<Button-1>', lambda event, view=len(self.preview_labels): self.enlarge_preview(view))
            visual.configure(cursor='hand2')
            self.preview_labels.append(visual)
        detail_labels = []
        detail_grid = tk.Frame(panel, bg='#202631')
        self.detail_expanded = True
        def toggle_details():
            self.detail_expanded = not self.detail_expanded
            if self.detail_expanded:
                detail_grid.pack(fill='x')
            else:
                detail_grid.pack_forget()
            self.detail_toggle.configure(text='收起学习与采集详情' if self.detail_expanded else '展开学习与采集详情')
        self.detail_toggle = tk.Button(panel, text='收起学习与采集详情', command=toggle_details, bg='#303949', fg='#f1f4f8', relief='flat', cursor='hand2')
        self.detail_toggle.pack(anchor='w', pady=(4, 0))
        for index, (label, var, color) in enumerate([('鼠标动作', self.control_details, '#d7e6ff'), ('学习情况', self.statistics, '#b0c0d4'), ('自主目标', self.goal_text, '#69cfbd'), ('画面采集', self.capture_text, '#b0c0d4'), ('最近一次异常', self.issue, '#ffbb85')]):
            block = tk.Frame(detail_grid, bg='#202631')
            block.grid(row=index // 2, column=index % 2, sticky='nsew', padx=(0, 6), pady=(0 if compact else 2, 0 if compact else 1))
            tk.Label(block, text=label, bg='#202631', fg='#8c9bb0', anchor='w', font=('Microsoft YaHei UI', 9, 'bold')).pack(anchor='w')
            detail = tk.Label(block, textvariable=var, bg='#202631', fg=color, anchor='w', justify='left', font=('Microsoft YaHei UI', 9))
            detail.pack(fill='x')
            detail_labels.append(detail)
        detail_grid.pack(fill='x')
        detail_grid.columnconfigure(0, weight=1, uniform='detail')
        detail_grid.columnconfigure(1, weight=1, uniform='detail')
        def resize_details(event):
            width = max(1, event.width - 20)
            for detail in detail_labels:
                detail.configure(wraplength=max(130, (width - 25) // 2))
            if self.latest_preview is not None and getattr(self, '_preview_width', None) != width:
                self._preview_width = width
                self.root.after_idle(lambda: self.render_preview(self.latest_preview))
        self.latest_preview = None
        panel.bind('<Configure>', resize_details, add='+')
        bind_scroll(panel)

    def report_storage(self):
        if self.exit_stop.is_set():
            return
        if time.monotonic() - self.storage_checked_at >= 30.:
            self.storage_checked_at = time.monotonic()
            folder = self.folder
            def measure():
                try:
                    target = next((path for path in (folder, *folder.parents) if path.exists()), Path.home())
                    space = shutil.disk_usage(target)
                    self.post('storage', f'数据文件夹：{folder} · 磁盘可用 {space.free / 1073741824.:.1f} GB')
                except (OSError, ValueError) as error:
                    self.post('storage', '存储状态检测失败：' + str(error)[:75])
            threading.Thread(target=measure, daemon=True).start()
        self.root.after(3000, self.report_storage)

    def change_explore_permission(self):
        if self.explore_check.get():
            self.explore_permission.set()
            self.status.set('探索性点击已授权；仅选定窗口的标准按钮/标签/链接，点击可能修改窗口数据')
        else:
            self.explore_permission.clear()
            self.status.set('探索性点击已关闭；保留已示范动作与移动学习')

    def input_generation_current(self, generation):
        with self.human_lock:
            return self.human_event_id == generation and not self.user_override.is_set()

    def change_takeover_permission(self):
        selected = self.listing.get(self.combo_var.get())
        if self.takeover_check.get() and selected is not None:
            self.takeover_window = selected
            self.takeover_permission.set()
            self.status.set('已授权当前窗口无人值守鼠标控制；仅前台且用户空闲时接管，真实输入随时中断')
        else:
            self.takeover_permission.clear()
            self.takeover_window = None
            if self.mode == 'control':
                self.emergency_stop('已撤销自动接管授权，马上释放鼠标')
            else:
                self.status.set('无人值守控制未授权；继续静默学习所选窗口')

    def revoke_takeover_permission(self):
        self.takeover_permission.clear()
        self.takeover_window = None
        self.takeover_check.set(False)
        if self.mode == 'control':
            self.emergency_stop('已撤销自动接管授权，马上释放鼠标')

    def preload_selected(self, event=None):
        if event is not None or self.takeover_window != self.listing.get(self.combo_var.get()):
            self.revoke_takeover_permission()
        self.human_input()
        self.task_failed = False
        self.status.set('已选择目标窗口，正在自动准备观察；所有经验只保存在所选文件夹')
        self.root.after_idle(self.begin_observing)
        if self.hardware_probe_thread is None or not self.hardware_probe_thread.is_alive():
            def preview_hardware():
                devices = detect_gpu()
                self.nvidia_present = any('nvidia' in name.lower() for name in devices)
                if self.mode == 'idle' and not self.exit_stop.is_set():
                    self.post('gpu_state', ('已识别：' + '、'.join(devices[:3]) + ' · 等待真实模型计算验证') if devices else '未确认独立 GPU · 控制仍可立即启动')
            self.hardware_probe_thread = threading.Thread(target=preview_hardware, daemon=True)
            self.hardware_probe_thread.start()
        if os.name != 'nt' or self.mode != 'idle' or self.switching_folder or self.brain is not None:
            return
        selected = self.combo_var.get()
        self.selected_key = selected
        hwnd = self.listing.get(selected)
        if hwnd is None or (self.initializer is not None and self.initializer.is_alive()):
            return
        source_folder = self.folder
        folder, environment_code = environment_for(source_folder, hwnd, selected)
        self.start_capture_preparation()
        def prepare():
            try:
                with self.engine_init_lock:
                    if self.exit_stop.is_set() or self.brain is not None or self.selected_key != selected or self.folder != source_folder:
                        return
                    provisional = LiteBrain(folder)
                    if self.exit_stop.is_set() or self.selected_key != selected or self.folder != source_folder or self.brain is not None:
                        provisional.close()
                        return
                    self.brain = provisional
                    self.brain_folder = folder
                    self.data_folder = folder
                    self.environment_code = environment_code
                    self.post('backend', provisional.label + ' · GPU 正在准备')
                self.start_acceleration()
            except Exception as error:
                if not self.exit_stop.is_set():
                    self.post('accelerator', '提前准备未完成：' + str(error)[:100])
            finally:
                if self.selected_key != selected and not self.exit_stop.is_set():
                    self.post('preload_again', selected)
        self.initializer = threading.Thread(target=prepare, daemon=True)
        self.initializer.start()

    def human_input(self, mouse_event=None, keyboard=False):
        now = time.monotonic()
        with self.human_lock:
            self.user_override.set()
            elapsed = now - self.human_last_input
            if elapsed > .5:
                self.human_gaps.append(elapsed)
            self.human_last_input = now
            self.human_event_id += 1
            if mouse_event is not None:
                self.human_events.append((self.human_event_id, now, *mouse_event))
        if self.mode == 'control' and not self.control_stop.is_set():
            self.mouse_monitor_armed.clear()
            self.release_signal.set()
            if keyboard:
                self.keyboard_stopped_control.set()
                self.emergency_stop('检测到真实键盘输入，已停止鼠标控制', fast=True)
            else:
                self.control_state = '安全暂停'
                self.control_heartbeat = 0.

    def idle_delay(self):
        double_click = float(u.GetDoubleClickTime()) / 1000. if os.name == 'nt' else .5
        baseline = max(double_click * 32., time.get_clock_info('monotonic').resolution)
        with self.human_lock:
            gaps = sorted(g for g in self.human_gaps if g > double_click)
        if len(gaps) < max(4, math.isqrt(self.human_gaps.maxlen)):
            return baseline
        center = gaps[len(gaps) // 2]
        deviation = sorted(abs(value - center) for value in gaps)[len(gaps) // 2]
        typical_pause = center + 3. * deviation
        return max(baseline, min(typical_pause, gaps[int(.9 * (len(gaps) - 1))]))

    def human_idle(self):
        with self.human_lock:
            last = self.human_last_input
        timeout = self.idle_delay()
        if time.monotonic() - last < timeout:
            return False
        if self.mode != 'control':
            observed = system_idle_seconds()
            if observed is None or observed < timeout:
                return False
        return True

    def takeover_allowed(self):
        if (os.name != 'nt' or not self.takeover_permission.is_set() or
                self.takeover_window != self.session_hwnd or not self.human_idle() or
                not self.keyboard_ready.is_set()):
            return False
        if time.monotonic() - self.keyboard_alive_at >= max(1., self.watchdog_limit):
            return False
        try:
            tracked = self.active_io.down if self.mode == 'control' and self.active_io is not None else {}
            eligible = (interactive_desktop() and int(u.GetForegroundWindow() or 0) == int(self.session_hwnd or 0) and
                        not any(u.GetAsyncKeyState(vk) & 0x8000 for name, vk in (('l', 1), ('r', 2), ('m', 4)) if not tracked.get(name, False)) and
                        not any(u.GetAsyncKeyState(vk) & 0x8000 for vk in (5, 6)) and
                        not any(u.GetAsyncKeyState(vk) & 0x8000 for vk in range(7, 256)))
            if not eligible:
                return False
            with self.human_lock:
                delay = self.idle_delay()
                if time.monotonic() - self.human_last_input < delay:
                    return False
                if self.mode != 'control':
                    system_idle = system_idle_seconds()
                    if system_idle is None or system_idle < delay:
                        return False
                if not self.keyboard_ready.is_set() or self.control_stop.is_set() or self.exit_stop.is_set():
                    return False
                self.user_override.clear()
                if self.active_io is not None:
                    self.active_io.input_generation = self.human_event_id
                return True
        except (OSError, ValueError, AttributeError):
            return False

    def begin_observing(self):
        if self.exit_stop.is_set() or self.switching_folder or self.pending_folder is not None:
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None or os.name != 'nt':
            return
        if self.mode in ('observe', 'control'):
            if self.session_hwnd != hwnd:
                self.handoff_pending = False
                if self.mode == 'observe':
                    self.observer_stop.set()
                else:
                    self.emergency_stop('目标窗口已更换，正在归还控制权')
            return
        if self.mode != 'idle':
            return
        if self.worker is not None and self.worker.is_alive():
            self.root.after(150, self.begin_observing)
            return
        if time.monotonic() < self.next_observer_retry:
            self.root.after(500, self.begin_observing)
            return
        self.session_hwnd = hwnd
        self.data_folder, self.environment_code = environment_for(self.folder, hwnd, self.combo_var.get())
        self.control_stop.clear()
        self.observer_stop.clear()
        self.mode = 'observe'
        self.task_failed = False
        self.task_outcome = None
        self.phase.set('用户观察与学习')
        self.set_progress(0, '观察系统准备中')
        self.worker = threading.Thread(target=self.observe_job, args=(hwnd,), daemon=True)
        self.worker.start()

    def apply_pending_folder(self):
        if self.pending_folder is None or self.mode != 'idle':
            return
        if (self.worker is not None and self.worker.is_alive()) or (self.online_worker is not None and self.online_worker.is_alive()):
            self.root.after(150, self.apply_pending_folder)
            return
        folder = self.pending_folder
        self.pending_folder = None
        self.apply_folder(folder)

    def observe_job(self, hwnd):
        device = None
        previous = None
        last_action_time = time.monotonic()
        prior_id = 0
        last_save = time.monotonic()
        ready_reported = False
        announced = False
        observation_feedback = Feedback()
        demonstration_atlas = None
        stop = AnyStop(self.observer_stop, self.exit_stop)
        try:
            self.load(stop)
            if stop.is_set():
                return
            self.post('progress', (100. / 3., '初始化 1/3 · 学习引擎就绪'))
            demonstration_atlas = GoalAtlas(self.data_folder)
            self.goal_atlas = demonstration_atlas
            device = WindowsIO(hwnd)
            device.keyboard_guard = self.keyboard_ready
            self.post('progress', (200. / 3., '初始化 2/3 · 截图设备已创建'))
            self.start_online()
            while not stop.is_set():
                if self.session_hwnd != hwnd or not u.IsWindow(hwnd):
                    break
                if not self.keyboard_ready.is_set():
                    stop.wait(.1)
                    continue
                if self.online_error is not None:
                    problem = self.online_error
                    self.online_error = None
                    self.recover_learning_backend(problem)
                    if stop.is_set():
                        break
                    self.start_online()
                if self.upgrade_backend():
                    self.start_online()
                elif not self.brain.accelerated and time.monotonic() >= self.next_backend_retry:
                    self.start_acceleration()
                region = device.region()
                if self.takeover_allowed():
                    self.post('phase', '无人输入 · 准备自主鼠标控制')
                    self.post('takeover', hwnd)
                    break
                if region is None or not device.foreground():
                    previous = None
                    announced = False
                    self.post('status', '人工学习等待中：只观察已选择且处于前台的窗口；人仍在操作时绝不改变窗口焦点')
                    stop.wait(.15)
                    continue
                started = time.monotonic()
                self.control_interval = max(device.display_period, device.last_capture_ms / 1000., started - last_action_time)
                try:
                    frame = device.image(region)
                    if not device.last_frame_valid or len(frame) != VIS_N:
                        previous = None
                        stop.wait(max(.03, device.display_period))
                        continue
                    frame_stamp = device.last_capture_stamp
                    if previous is not None and frame_stamp <= last_action_time:
                        stop.wait(max(.015, device.display_period))
                        continue
                    cursor = device.cursor()
                    held = device.keys()
                    with self.human_lock:
                        pending = tuple(event for event in self.human_events if event[0] > prior_id)
                    events = tuple(event for event in pending if event[1] <= frame_stamp)
                    current_event_id = events[-1][0] if events else prior_id
                    if any(event[1] > frame_stamp for event in pending):
                        stop.wait(max(.015, device.display_period))
                        continue
                    if started - self.preview_at > max(.3, device.last_capture_ms / 1000. * 3):
                        self.preview_at = started
                        self.post('preview', frame)
                    if previous is not None and events:
                        old_frame, old_cursor, old_held, old_meta, old_region, old_epoch = previous
                        if region == old_region and device.capture_epoch == old_epoch:
                            aligned = [event for event in events if last_action_time < event[1] <= frame_stamp]
                            elapsed = max(sys.float_info.epsilon, frame_stamp - last_action_time)
                            samples = demonstration_from_events(old_cursor, cursor, old_held, held, aligned, region, elapsed)
                            if samples:
                                isolated = len(samples) == 1 and len(aligned) == 1 and frame_stamp > aligned[0][1]
                                reward = 0.
                                change = 0.
                                advanced = False
                                if isolated:
                                    action, control, distance, transitions, scroll, duration, position, down = samples[0]
                                    outcome = {'action': action, 'ctrl': control, 'changed': bool(distance or transitions or scroll),
                                               'moved': distance, 'efficacy': 1., 'switches': transitions, 'blocked': False,
                                               'pending_scroll': False, 'scroll': scroll}
                                    reward, change, advanced = observation_feedback.assess(old_frame, frame, old_frame, outcome, cursor, region)
                                    reward = max(-1., min(1., reward))
                                    if demonstration_atlas is not None:
                                        demonstration_atlas.observe(old_frame, action, frame, reward, 1., advanced, True)
                                sample_time = last_action_time
                                previous_cursor = old_cursor
                                meta_before = old_meta
                                for action, control, distance, transitions, scroll, duration, position, down in samples:
                                    sample_time = min(frame_stamp, sample_time + duration)
                                    new_meta = self.create_meta(sample_time, region, position, previous_cursor, down, scroll, duration, change if isolated else 0.)
                                    self.brain.learn(old_frame, meta_before, action, frame if isolated else old_frame,
                                                     new_meta, reward if isolated else 0., True, duration,
                                                     control, control, action, 1., False, True)
                                    self.control_history.append((control[0] * control[2], control[1] * control[2], control[6], reward if isolated else 0.))
                                    self.observed_count += 1
                                    meta_before = new_meta
                                    previous_cursor = position
                                if self.observed_count % max(2, math.isqrt(max(1, self.observed_count))) < len(samples):
                                    reliable = '已采集单动作前后截图' if isolated else '连续动作仅模仿学习，未虚构动作结果'
                                    self.post('stats', f'人工示范 {self.observed_count} 条 · 短期经验 {len(self.brain.memory)} · 自主操作 {self.iterations} 次 · {reliable}')
                                    self.post('control', f'正在学习人工鼠标示范：分解 {len(samples)} 步 · 鼠标键变化 {sum(bool(part[3]) for part in samples)} · 滚轮 {sum(part[4] for part in samples):+d}')
                                    perf = self.brain.latest_perf if isinstance(self.brain, RemoteBrain) else {}
                                    if perf and self.brain.engine_backend == 'cuda':
                                        self.post('gpu_state', self.brain.label + (' · CUDA训练已实际执行' if perf.get('cuda_optimizer_steps', 0) else ' · CUDA模型已验证，正在等待训练') + f' · 累计训练 {perf.get("training_examples", 0)} 样本')
                    old_pos = previous[1] if previous is not None and previous[4] == region else cursor
                    old_dt = max(sys.float_info.epsilon, frame_stamp - last_action_time)
                    meta = self.create_meta(frame_stamp, region, cursor, old_pos, held, 0, old_dt, 0.)
                    previous = (frame, cursor, held, meta, region, device.capture_epoch)
                    last_action_time = frame_stamp
                    prior_id = current_event_id
                    if not ready_reported:
                        ready_reported = True
                        self.post('progress', (100, '初始化 3/3 · 已收到有效截图'))
                    if not announced:
                        announced = True
                        self.post('phase', '用户在 · 静默学习')
                    self.post('status', f'正在学习所选窗口的真实鼠标动作；' + (f'空闲约 {self.idle_delay():.0f} 秒且窗口位于前台时允许自主接管。' if self.takeover_permission.is_set() else '未启用无人值守控制，AI 不会发送鼠标动作。'))
                    if started - last_save >= max(12., math.sqrt(1. + self.observed_count)) and self.observed_count:
                        self.schedule_checkpoint()
                        last_save = started
                except (OSError, RuntimeError, ValueError, TimeoutError) as error:
                    self.post('status', '人工示范截图/学习暂不可用：' + str(error)[:100])
                    previous = None
                stop.wait(max(.015, device.display_period, device.last_capture_ms / 1000.))
        except Exception as error:
            self.next_observer_retry = time.monotonic() + 5.
            self.post('error', '观察模式初始化失败：' + str(error)[:135])
        finally:
            self.online_stop.set()
            if self.online_worker is not None and self.online_worker.is_alive():
                self.online_worker.join(timeout=5.)
            if device is not None:
                try:
                    device.close()
                except Exception:
                    pass
            if demonstration_atlas is not None:
                try:
                    demonstration_atlas.save()
                except (OSError, ValueError) as error:
                    self.post('status', '人工示范目标保存暂不可用：' + str(error)[:90])
                finally:
                    if self.goal_atlas is demonstration_atlas:
                        self.goal_atlas = None
            if self.brain is not None:
                try:
                    if self.saver is not None and self.saver.is_alive():
                        self.saver.join(timeout=8.)
                    self.brain.save()
                except Exception as error:
                    self.post('status', '自动保存暂不可用：' + str(error)[:90])
            self.post('done', 'observe')

    def update_buttons(self):
        available = self.mode in ('idle', 'observe') and not self.switching_folder
        self.folder_button.configure(state='normal' if available else 'disabled')

    def set_progress(self, fraction, stage, terminal=None):
        requested = min(100., max(0., float(fraction)))
        if requested == 0. and terminal is None:
            percent = 0.
        else:
            percent = max(self.progress_value.get(), requested)
        if terminal in ('failed', 'cancelled'):
            percent = min(percent, 99.)
        self.progress_value.set(percent)
        ending = ' · 未完成' if terminal == 'failed' else (' · 已取消' if terminal == 'cancelled' else '')
        self.progress_text.set(f'{stage} · {percent:.0f}%{ending}')

    def post(self, kind, value):
        if kind in ('control', 'stats', 'capture', 'accelerator', 'status', 'goal', 'preview', 'fps', 'gpu_state', 'storage'):
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
                if not self.task_failed:
                    self.set_progress(*val)
            elif kind == 'folder_changed':
                folder, transferred = val
                folder = Path(folder)
                self.folder_origin_default = False
                self.folder = folder
                self.data_folder = folder
                self.folder_text.set(str(folder))
                self.storage_checked_at = 0.
                self.backend.set('未启动')
                self.issue.set('无')
                self.task_failed = False
                self.phase.set('空闲')
                self.status.set('已切换数据目录，旧经验与运行时已迁移' if transferred else '已切换数据目录，原有目录独立保留')
                self.switching_folder = False
                self.mode = 'idle'
                self.set_progress(100, '文件夹切换完成')
                self.root.after_idle(self.preload_selected)
            elif kind == 'folder_failed':
                self.task_failed = True
                self.set_progress(self.progress_value.get(), '文件夹切换失败', 'failed')
                self.switching_folder = False
                self.mode = 'idle'
                self.issue.set(str(val))
                self.status.set('切换文件夹失败：' + str(val))
                self.phase.set('需要检查')
            elif kind == 'takeover':
                self.handoff_pending = bool(val == self.session_hwnd)
            elif kind == 'task_result':
                if not self.task_failed or str(val) == '失败':
                    self.task_outcome = str(val)
            elif kind == 'done':
                if self.mode != 'closed' and val == self.mode:
                    self.mode = 'idle'
                    if not self.task_failed:
                        self.phase.set('空闲' if self.task_outcome is None else self.task_outcome)
                    label = ('鼠标控制结束' if val == 'control' else '观察模式结束') + ' · ' + (self.task_outcome or ('异常' if self.task_failed else '已完成'))
                    if self.task_failed:
                        self.set_progress(self.progress_value.get(), label, 'failed')
                    elif self.progress_value.get() < 100.:
                        self.set_progress(self.progress_value.get(), label, 'cancelled')
                    else:
                        self.set_progress(100, label)
                    self.control_state = '空闲' if val == 'control' else self.control_state
                    if self.pending_folder is not None:
                        self.root.after_idle(self.apply_pending_folder)
                    elif val == 'observe' and self.handoff_pending and self.session_hwnd == self.listing.get(self.combo_var.get()):
                        self.handoff_pending = False
                        self.root.after_idle(self.start)
                    elif val in ('control', 'observe'):
                        self.handoff_pending = False
                        self.root.after_idle(self.begin_observing)
            elif kind == 'preload_again':
                if self.mode == 'idle' and self.selected_key != val and self.brain is None:
                    self.initializer = None
                    self.preload_selected()
            elif kind == 'error':
                had_error = True
                self.task_failed = True
                self.task_outcome = '失败'
                self.issue.set(val)
                self.phase.set('异常')
                self.status.set('发生问题：' + val)
                self.set_progress(self.progress_value.get(), '任务异常', 'failed')
        with self.fast_messages_lock:
            updates = self.fast_messages
            self.fast_messages = {}
        if 'status' in updates and not had_error and not self.task_failed and self.mode != 'closed':
            self.status.set(updates['status'])
        if 'stats' in updates:
            self.statistics.set(updates['stats'])
            self.learning_summary.set('学习：' + ' · '.join(str(updates['stats']).split(' · ')[:4]))
        if 'capture' in updates:
            self.capture_text.set(updates['capture'])
        if 'fps' in updates:
            self.fps_text.set(updates['fps'])
        if 'gpu_state' in updates:
            self.gpu_state.set(updates['gpu_state'])
        if 'storage' in updates:
            self.storage_state.set(updates['storage'])
        if 'goal' in updates:
            self.goal_text.set(updates['goal'])
        if 'accelerator' in updates and self.brain is not None and not self.brain.accelerated and self.mode != 'closed':
            self.backend.set(self.brain.label + ' · ' + str(updates['accelerator'])[:105])
        if 'preview' in updates:
            self.render_preview(updates['preview'])
        if 'control' in updates:
            latest_control = updates['control']
        if latest_control is not None:
            self.control_details.set(latest_control)
        if os.name == 'nt':
            healthy = self.keyboard_ready.is_set() and self.keyboard_alive_at and time.monotonic() - self.keyboard_alive_at < max(1., self.watchdog_limit)
            self.safety_text.set(('鼠标' + self.control_state + ' · ' if self.mode == 'control' else '') + ('真实鼠标/键盘活动检测在线 · 人工操作优先' if healthy else '输入监控恢复中 · 禁止自主动作'))
            if self.mode == 'control' and not healthy:
                self.status.set('键盘监控正在恢复；暂停鼠标操作')
        if self.start_queued is not None:
            selection = self.start_queued
            if self.mode != 'idle' or selection != self.combo_var.get():
                self.start_queued = None
            elif self.keyboard_ready.is_set() and time.monotonic() - self.keyboard_alive_at < max(1., self.watchdog_limit):
                self.start_queued = None
                self.root.after_idle(self.start)
        if not self.exit_stop.is_set():
            self.update_buttons()
            self.root.after(10 if not self.message.empty() else 90, self.pump)

    def render_preview(self, frames):
        if not isinstance(frames, bytes) or len(frames) != VIS_N:
            return
        self.latest_preview = frames
        try:
            available = max(160, (self.preview_frame.winfo_width() - 22) // 2)
            scale = max(1, math.ceil(VIS_W / available))
            if getattr(self, '_preview_scale', None) == scale and frames is getattr(self, '_preview_rendered', None):
                return
            pictures = []
            for view in range(2):
                plane = frames[view * CHANNELS * PIXELS:(view + 1) * CHANNELS * PIXELS]
                interleaved = bytearray(PIXELS * CHANNELS)
                for channel in range(CHANNELS):
                    interleaved[channel::CHANNELS] = plane[channel * PIXELS:(channel + 1) * PIXELS]
                raw = f'P6\n{VIS_W} {VIS_H}\n255\n'.encode('ascii') + interleaved
                photo = tk.PhotoImage(data=raw, format='PPM')
                if scale > 1:
                    photo = photo.subsample(scale, scale)
                pictures.append(photo)
            for item, photo in zip(self.preview_labels, pictures):
                item.configure(image=photo, text='', height=photo.height(), width=photo.width())
            self.preview_photos = pictures
            self._preview_scale = scale
            self._preview_rendered = frames
        except (ValueError, tk.TclError, MemoryError):
            return

    def enlarge_preview(self, view):
        frames = getattr(self, 'latest_preview', None)
        if not isinstance(frames, bytes) or len(frames) != VIS_N:
            return
        window = tk.Toplevel(self.root)
        window.title('全窗口概览' if view == 0 else '鼠标附近细节')
        window.configure(bg='#10131a')
        plane = frames[view * CHANNELS * PIXELS:(view + 1) * CHANNELS * PIXELS]
        data = bytearray(CHANNELS * PIXELS)
        for channel in range(CHANNELS):
            data[channel::CHANNELS] = plane[channel * PIXELS:(channel + 1) * PIXELS]
        photo = tk.PhotoImage(data=f'P6\n{VIS_W} {VIS_H}\n255\n'.encode('ascii') + data, format='PPM')
        scale = max(1, math.ceil(VIS_W / max(1, self.root.winfo_screenwidth() - 80)), math.ceil(VIS_H / max(1, self.root.winfo_screenheight() - 120)))
        if scale > 1:
            photo = photo.subsample(scale, scale)
        visual = tk.Label(window, image=photo, bg='#10131a')
        visual.image = photo
        visual.pack(padx=10, pady=10)

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
            selected_hwnd = self.listing.get(self.combo_var.get())
            self.listing = {f'{name[:76]}  [0x{hwnd:X}]': hwnd for hwnd, name in windows}
            self.combo['values'] = list(self.listing)
            self.combo_var.set(next((label for label, hwnd in self.listing.items() if hwnd == selected_hwnd), ''))
        except Exception as ex:
            self.status.set('无法列举窗口：' + str(ex)[:90])
        if self.mode != 'closed' and not self.exit_stop.is_set():
            self.refresh_after = self.root.after(max(250, round(1000 * math.sqrt(max(1, len(self.listing))))), self.refresh)

    def choose_folder(self):
        if self.switching_folder or self.mode not in ('idle', 'observe'):
            self.status.set('AI 正在自主操作，移动鼠标即可交还控制，再选择数据目录')
            return
        new = filedialog.askdirectory(parent=self.root, initialdir=str(self.folder), title='选择 AI 数据存放文件夹')
        if not new:
            return
        folder = Path(new)
        self.revoke_takeover_permission()
        if self.mode == 'observe':
            self.pending_folder = folder
            self.observer_stop.set()
            self.online_stop.set()
            self.status.set('正在安全保存旧文件夹后切换')
            return
        self.apply_folder(folder)

    def apply_folder(self, folder):
        if folder == self.folder:
            self.preload_selected()
            return
        if any(worker is not None and worker.is_alive() for worker in (self.worker, self.online_worker)):
            self.status.set('控制线程仍在退出，请稍后更换目录')
            return
        source_folder = self.folder
        migrate_on_switch = self.folder_origin_default
        self.task_failed = False
        self.selected_key = ''
        self.switching_folder = True
        self.mode = 'switching'
        self.phase.set('保存并切换文件夹')
        self.status.set('正在后台保存旧数据，界面保持响应')
        self.set_progress(0, '切换文件夹')
        self.update_buttons()
        def transition():
            try:
                self.cancel_acceleration()
                if self.initializer is not None and self.initializer.is_alive():
                    self.initializer.join()
                for task in (self.acceleration_thread, self.capture_worker):
                    if task is not None and task.is_alive() and task is not threading.current_thread():
                        task.join()
                self.post('progress', (100. / 3., '切换 1/3 · 计算任务已结束'))
                if self.saver is not None and self.saver.is_alive():
                    self.saver.join()
                if self.exit_stop.is_set():
                    return
                previous = self.brain
                if previous is not None:
                    previous.save()
                    self.post('progress', (200. / 3., '切换 2/3 · 数据已保存'))
                    previous.close()
                if self.exit_stop.is_set():
                    return
                self.brain = None
                self.brain_folder = None
                self.acceleration_attempt_folder = None
                self.next_backend_retry = 0.
                self.acceleration_failures = 0
                self.acceleration_retry_signature = None
                self.nvidia_present = None
                self.backend_faults = {}
                self.audit_sum = 0.
                self.audit_samples = 0
                transferred = False
                if migrate_on_switch and not self.exit_stop.is_set():
                    self.post('progress', (85., '切换 3/3 · 整理默认数据目录'))
                    try:
                        transferred = migrate_default_data(source_folder, folder)
                    except (OSError, shutil.Error) as error:
                        self.post('status', '原目录数据未迁移，已保留原始文件：' + str(error)[:95])
                self.post('folder_changed', (str(folder), transferred))
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
        if os.name != 'nt' or self.exit_stop.is_set() or self.brain is None:
            return
        upgrade_cuda = isinstance(self.brain, RemoteBrain) and self.brain.engine_backend == 'directml'
        if self.brain.accelerated and not upgrade_cuda:
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
            started_at = time.monotonic()
            try:
                cancel = AnyStop(self.exit_stop, token)
                devices = detect_gpu()
                self.nvidia_present = (any('nvidia' in name.lower() for name in devices)
                                       or bool(cuda_driver_version()) or bool(nvidia_driver_info()))
                if upgrade_cuda and not self.nvidia_present:
                    self.post('gpu_state', 'DirectML 已验证运行 · 正在等待 NVIDIA 驱动可识别后重试 CUDA')
                    return
                stable_drivers = tuple(line.rsplit(',', 1)[0].strip() for line in nvidia_driver_info())
                retry_signature = (tuple(devices), stable_drivers, cuda_driver_version())
                with self.acceleration_lock:
                    if retry_signature != self.acceleration_retry_signature:
                        self.acceleration_retry_signature = retry_signature
                        self.acceleration_failures = 0
                        self.next_backend_retry = 0.
                if devices:
                    self.post('gpu_state', '硬件已识别：' + '、'.join(devices[:2]) + ' · 驱动/模型计算验证中 · GPU尚未接管')
                    self.post('accelerator', '已识别 ' + '、'.join(devices[:2]) + '；正在后台验证 GPU 计算，控制无需等待')
                else:
                    self.post('gpu_state', '显卡硬件尚未确认 · 正在检测驱动和计算组件 · 当前基础引擎可用')
                    self.post('accelerator', '正在后台检测计算设备与准备加速，控制无需等待')
                gpu_only = isinstance(self.brain, RemoteBrain)
                last_failure = ['']
                def hardware_report(message):
                    self.post('accelerator', message)
                    if any(word in message for word in ('验证失败', '安装失败', '未通过', '驱动接口尚未就绪')):
                        last_failure[0] = message[:125]
                    if message.startswith('驱动接口已确认'):
                        self.post('gpu_state', 'NVIDIA 已识别 · CUDA驱动可用 · PyTorch模型计算验证中 · 尚未接管')
                    elif message.startswith('已识别 NVIDIA 设备，但'):
                        self.post('gpu_state', 'NVIDIA 已识别 · CUDA驱动未通过检测 · 正在尝试DirectML')
                ready = load_brain(folder, hardware_report, cancel, runtime_folder=runtime_folder, gpu_only=gpu_only, cuda_only=upgrade_cuda)
                if ready is not None and ready.accelerated:
                    self.post('gpu_state', '显卡已识别 · ' + ready.label + ' · 模型计算验证通过 · 等待接管')
                may_upgrade = (isinstance(self.brain, LiteBrain) or
                               isinstance(self.brain, RemoteBrain) and ready is not None and ready.accelerated and
                               (not self.brain.accelerated or self.brain.engine_backend == 'directml' and ready.engine_backend == 'cuda'))
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
                    self.post('gpu_state', ('DirectML 正常运行 · CUDA 升级待验证 · ' if upgrade_cuda else 'GPU训练尚未通过验证 · 当前由基础引擎控制 · ') + (last_failure[0] or '已记录后端诊断'))
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
                        if ready.engine_backend == 'directml' and self.nvidia_present:
                            self.next_backend_retry = time.monotonic() + max(10., min(600., time.monotonic() - started_at))
                        self.acceleration_ready = ready
                        self.post('accelerator', ready.label + ' 已就绪，正在等待安全切换')
                        ready = None
                    elif valid and ready is None:
                        self.acceleration_failures += 1
                        elapsed = max(time.monotonic() - started_at, .001)
                        self.next_backend_retry = time.monotonic() + min(3600., elapsed * (2 ** min(self.acceleration_failures, 10)))
                    elif valid:
                        self.acceleration_failures = 0
                        self.next_backend_retry = 0.
                if ready is not None:
                    ready.close()

        self.acceleration_thread = threading.Thread(target=prepare, daemon=True)
        self.acceleration_thread.start()

    def upgrade_backend(self, io=None):
        with self.acceleration_lock:
            candidate = self.acceleration_ready if self.acceleration_folder == self.data_folder else None
            if candidate is None or (self.saver is not None and self.saver.is_alive()):
                return False
            if self.online_worker is not None and self.online_worker.is_alive() and self.online_stop.is_set():
                return False
            if self.control_stop.is_set() and self.mode == 'control':
                return False
            self.acceleration_ready = None
        previous = self.brain
        previous_folder = self.brain_folder
        if previous is None or self.exit_stop.is_set():
            candidate.close()
            return False
        if io is not None:
            self.backend_recovering.set()
            self.mouse_monitor_armed.clear()
        was_online = self.online_worker is not None and self.online_worker.is_alive()
        try:
            if io is not None:
                io.quick_release()
            if was_online:
                self.online_stop.set()
                if isinstance(previous, RemoteBrain):
                    previous.cancel_train()
                self.online_worker.join(timeout=max(.5, min(1.5, self.watchdog_limit * .35)))
                if self.online_worker.is_alive():
                    with self.acceleration_lock:
                        if self.acceleration_ready is None and self.acceleration_folder == self.data_folder:
                            self.acceleration_ready = candidate
                            candidate = None
                    self.post('accelerator', '等待当前训练批安全退出后再切换 GPU')
                    return False
            self.online_worker = None
            if self.control_stop.is_set() and self.mode == 'control':
                raise InterruptedError('收到键盘急停，取消后端切换')
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
                boundary_matches = (difference == len(old_rows) and new_count == 0) or (0 < difference < len(old_rows) and new_last == old_rows[-difference - 1])
                if difference > 0 and boundary_matches:
                    candidate.append_records(old_rows[-difference:], old_steps)
                else:
                    candidate.sync_fast(old_rows, max(old_steps, new_steps))
            if self.control_stop.is_set() and self.mode == 'control':
                raise InterruptedError('收到键盘急停，取消后端切换')
            self.brain = candidate
            self.brain_folder = self.data_folder
            self.next_backend_retry = 0.
            self.acceleration_failures = 0
            self.post('backend', candidate.label)
            self.post('gpu_state', (candidate.label + ' · 已通过模型计算验证 · GPU已实际接管' if candidate.accelerated else '当前由 ' + candidate.label + ' 执行 · GPU未接管'))
            if io is not None and not self.control_stop.is_set():
                try:
                    self.start_online()
                except Exception as error:
                    self.post('status', '新后端在线训练尚未启动：' + str(error)[:75])
            try:
                previous.close()
            except Exception as error:
                self.post('status', '旧计算资源释放出现问题：' + str(error)[:70])
            self.post('status', '已切换到 ' + candidate.label + '，交互经验已同步')
            if candidate.engine_backend == 'directml' and self.nvidia_present:
                self.start_acceleration()
            return True
        except Exception as error:
            if candidate is not None:
                if self.brain is candidate:
                    self.brain = previous
                    self.brain_folder = previous_folder
                candidate.close()
            if self.brain is previous and was_online and self.online_worker is None and not self.control_stop.is_set():
                try:
                    self.start_online()
                except Exception:
                    pass
            self.post('accelerator', '后端切换未完成，保留原学习引擎：' + str(error)[:90])
            return False
        finally:
            if io is not None:
                self.backend_recovering.clear()
                self.control_heartbeat = time.monotonic()

    def load(self, task_stop):
        self.start_capture_preparation()
        with self.engine_init_lock:
            if self.brain is not None and self.brain_folder != self.data_folder:
                self.cancel_acceleration()
                self.brain.save()
                self.brain.close()
                self.brain = None
                self.brain_folder = None
            if task_stop.is_set() or self.exit_stop.is_set():
                return
            if self.brain is None:
                self.post('phase', '快速启动学习引擎')
                self.post('status', '正在加载已有经验；如存在 NVIDIA 显卡，将自动安装和验证 CUDA（就绪前使用临时基础引擎）')
                self.brain = LiteBrain(self.data_folder)
                if self.mode == 'control':
                    self.post('progress', (25, '初始化 1/4 · 学习引擎已加载'))
                self.brain_folder = self.data_folder
                self.post('backend', self.brain.label)
        if not self.upgrade_backend():
            self.start_acceleration()

    def start_capture_preparation(self):
        if getattr(self, 'capture_worker', None) is not None and self.capture_worker.is_alive():
            return
        folder = self.folder
        self.capture_worker = threading.Thread(target=ensure_capture, args=(folder, lambda msg: self.post('capture', str(msg)[:140]), self.exit_stop), daemon=True)
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
            choices.extend(('cuda', path) for path in sorted(runtime_folder.glob('.runtime_cuda_cu*'), reverse=True) if path.name.endswith('_' + python_runtime_id()) and runtime_valid(path, path.name[len('.runtime_'):].rsplit('_' + python_runtime_id(), 1)[0]))
            choices.append(('cuda', None))
            directml = managed_runtime(runtime_folder, 'directml')
            if runtime_valid(directml, 'directml'):
                choices.append(('directml', directml))
            choices.append(('directml', None))
            cpu = managed_runtime(runtime_folder, 'cpu')
            choices.extend([('cpu', cpu if runtime_valid(cpu, 'cpu') else None), ('cpu', None)])
            seen = set()
            backup = None
            failures_seen = []
            recovery_cancel = AnyStop(self.exit_stop, self.control_stop)
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

    def emergency_stop(self, reason, fast=False):
        self.user_override.set()
        self.control_stop.set()
        self.release_signal.set()
        self.control_state = '已停止'
        self.mouse_monitor_armed.clear()
        self.control_heartbeat = 0.
        self.online_stop.set()
        if not fast and isinstance(self.brain, RemoteBrain):
            self.brain.cancel_train()
        active = self.active_io
        if not fast and active is not None and (self.release_worker is None or not self.release_worker.is_alive()):
            def release_now():
                error = None
                for attempt in range(3):
                    try:
                        active.halt()
                        if not any(active.down.values()):
                            return
                    except Exception as failure:
                        error = failure
                    if not self.exit_stop.wait(.012 * (attempt + 1)):
                        continue
                self.post('error', '鼠标按键释放未确认：' + str(error or 'Windows 输入状态未同步')[:110])
            self.release_worker = threading.Thread(target=release_now, daemon=True)
            self.release_worker.start()
        if reason:
            self.post('status', reason)

    def online_job(self, brain):
        delay = max(sys.float_info.epsilon, self.control_interval)
        next_memory_check = 0.
        pressure = 0.
        while not self.online_stop.is_set() and not self.exit_stop.is_set() and not self.control_stop.is_set():
            if self.brain is not brain:
                return
            if self.backend_recovering.is_set() or (self.mode != 'observe' and not self.mouse_monitor_armed.is_set()):
                if self.online_stop.wait(max(delay, self.control_interval, .01)):
                    return
                continue
            started = time.monotonic()
            try:
                with brain.save_lock:
                    train_count = sum(not row[12] for row in brain.memory)
                if train_count >= 2:
                    if isinstance(brain, RemoteBrain) and brain.inference_interval and brain.online_train_cost >= max(0., brain.inference_interval - brain.recent_inference_cost):
                        self.online_stop.wait(max(brain.inference_interval, brain.online_train_cost, brain.recent_inference_cost))
                    else:
                        brain.train(1, self.online_stop)
            except Exception as ex:
                self.online_error = ex
                self.online_stop.set()
                return
            elapsed = time.monotonic() - started
            now = time.monotonic()
            if now >= next_memory_check:
                pressure = memory_pressure()
                next_memory_check = now + max(1., math.log2(2. + REPLAY_LIMIT))
            delay = max(elapsed, self.control_interval, float(getattr(brain, 'recent_inference_cost', 0.)), .01) * (1. + 3. * pressure)
            if self.online_stop.wait(delay):
                return

    def start_online(self):
        if self.brain is None:
            return
        if self.online_worker is not None and self.online_worker.is_alive():
            return
        self.online_error = None
        self.online_stop.clear()
        if isinstance(self.brain, RemoteBrain):
            self.brain.reset_train_cancel()
        self.online_worker = threading.Thread(target=self.online_job, args=(self.brain,), daemon=True)
        self.online_worker.start()

    def start(self):
        if os.name != 'nt' or struct.calcsize('P') != 8:
            self.status.set('需要 Windows 11 x64 与 64 位 Python 运行环境')
            return
        if not self.keyboard_ready.wait(.3) or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
            self.start_queued = self.combo_var.get()
            self.status.set('键盘安全监控正在初始化，准备好后自动开始鼠标控制')
            return
        if self.mode != 'idle' or (self.worker is not None and self.worker.is_alive()):
            self.root.after(150, self.start)
            return
        if not self.takeover_allowed():
            self.handoff_pending = False
            self.root.after_idle(self.begin_observing)
            return
        if self.online_worker is not None and self.online_worker.is_alive():
            self.status.set('后台训练正在结束，即将自动交接给 AI')
            self.root.after(180, self.start)
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None:
            self.status.set('请先选择一个有效窗口')
            return
        self.data_folder, self.environment_code = environment_for(self.folder, hwnd, self.combo_var.get())
        try:
            if not u.IsWindow(hwnd):
                raise RuntimeError('所选窗口已经关闭，请刷新窗口列表')
            if int(u.GetForegroundWindow() or 0) != int(hwnd):
                self.status.set('目标窗口不在前台，保持被动观察；不会抢占当前窗口焦点')
                self.root.after_idle(self.begin_observing)
                return
            rect = RECT()
            point = POINT(0, 0)
            if not u.GetClientRect(hwnd, ctypes.byref(rect)) or not u.ClientToScreen(hwnd, ctypes.byref(point)):
                raise RuntimeError('无法获取目标窗口客户区')
            width, height = rect.right - rect.left, rect.bottom - rect.top
            if width < 8 or height < 8:
                raise RuntimeError('目标窗口客户区没有足够的安全光标范围')
            if not self.takeover_allowed():
                self.root.after_idle(self.begin_observing)
                return
            point_cursor = POINT()
            if not u.GetCursorPos(ctypes.byref(point_cursor)):
                raise RuntimeError('无法读取鼠标位置')
        except Exception as error:
            self.phase.set('无法启动')
            self.issue.set(str(error))
            self.status.set('鼠标无法进入所选窗口：' + str(error))
            return
        self.phase.set('窗口已激活 · 准备模型')
        self.fps_text.set('控制 FPS：正在采样')
        self.set_progress(0, '启动目标窗口')
        self.task_failed = False
        self.task_outcome = None
        self.keyboard_stopped_control.clear()
        self.issue.set('无')
        self.status.set('已授权的目标窗口准备接管；真实鼠标操作将暂停 AI，任意键盘按键停止控制')
        self.control_details.set('无人输入，等待模型就绪 · 鼠标尚未接管')
        self.control_stop.clear()
        self.backend_recovering.clear()
        self.mouse_monitor_armed.clear()
        self.mode = 'control'
        self.control_state = '准备中'
        self.worker = threading.Thread(target=self.control_job, args=(hwnd,), daemon=True)
        self.control_worker = self.worker
        self.worker.start()

    def wheel_delta(self):
        with self.wheel_lock:
            value = sum(self.wheel_events)
            self.wheel_events.clear()
        return value

    def safe_target(self, device):
        try:
            return bool(interactive_desktop() and device.foreground() and device.region() is not None)
        except (OSError, RuntimeError, ValueError):
            return False

    def pause_mouse(self, device, reason):
        self.mouse_monitor_armed.clear()
        self.control_state = '安全暂停'
        self.control_heartbeat = 0.
        if device is not None:
            device.quick_release()
        self.post('status', '安全暂停：' + reason + '；按任意键停止，用户空闲且条件恢复后继续')

    def safety_sentinel(self):
        canceled = False
        while not self.exit_stop.is_set():
            self.release_signal.wait(.012)
            self.release_signal.clear()
            if self.exit_stop.is_set():
                break
            active = self.active_io
            if self.mode == 'control' and not self.control_stop.is_set():
                if active is not None and active.keyboard_activity():
                    self.keyboard_stopped_control.set()
                    self.emergency_stop('检测到键盘输入，已停止鼠标控制')
                elif active is not None and not self.human_idle() and (self.control_state != '安全暂停' or any(active.down.values()) or active.release_uncertain):
                    try:
                        self.pause_mouse(active, '用户正在使用鼠标')
                    except Exception as error:
                        self.emergency_stop('无法确认鼠标按键已释放：' + str(error)[:90])
                elif not self.keyboard_ready.is_set() or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
                    self.keyboard_ready.clear()
                    try:
                        if self.control_state != '安全暂停':
                            self.pause_mouse(active, '键盘监控暂不可用')
                    except Exception as error:
                        self.emergency_stop('无法确认鼠标按键已释放：' + str(error)[:90])
                elif active is not None and self.mouse_monitor_armed.is_set() and not self.safe_target(active):
                    try:
                        self.pause_mouse(active, '目标窗口失去焦点或客户区不可用')
                    except Exception as error:
                        self.emergency_stop('无法确认鼠标按键已释放：' + str(error)[:90])
                elif not self.backend_recovering.is_set() and self.mouse_monitor_armed.is_set() and self.control_heartbeat > 0 and time.monotonic() - self.control_heartbeat > self.watchdog_limit:
                    try:
                        self.pause_mouse(active, '计算响应超时')
                    except Exception as error:
                        self.emergency_stop('无法确认鼠标按键已释放：' + str(error)[:90])
            if self.control_stop.is_set():
                if active is not None and (any(active.down.values()) or active.release_uncertain):
                    try:
                        active.halt()
                    except Exception:
                        pass
                if not canceled and isinstance(self.brain, RemoteBrain):
                    self.brain.cancel_train()
                canceled = True
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
                if code >= 0 and int(wparam) in (0x100, 0x104):
                    try:
                        key = ctypes.cast(lparam, ctypes.POINTER(KBDLLHOOKSTRUCT)).contents
                        self.human_input(keyboard=True)
                    except Exception:
                        self.human_input(keyboard=True)
                return u.CallNextHookEx(None, code, wparam, lparam)
            def scrolled(code, wparam, lparam):
                if code >= 0:
                    try:
                        event = ctypes.cast(lparam, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                        kind = int(wparam)
                        injected_by_ai = bool(event.flags & 0x01) and event.extra == AI_INPUT_MARK
                        if injected_by_ai:
                            if kind == 0x20A:
                                delta = ctypes.c_short((event.mouseData >> 16) & 0xffff).value
                                with self.wheel_lock:
                                    self.wheel_events.append(delta)
                        else:
                            key = {0x201: 'l+', 0x202: 'l-', 0x204: 'r+', 0x205: 'r-', 0x207: 'm+', 0x208: 'm-'}.get(kind, '')
                            delta = ctypes.c_short((event.mouseData >> 16) & 0xffff).value if kind == 0x20A else 0
                            self.human_input((key, int(event.pt.x), int(event.pt.y), delta))
                    except Exception:
                        self.human_input()
                return u.CallNextHookEx(None, code, wparam, lparam)
            key_callback = KBDPROC(pressed)
            mouse_callback = MSPROC(scrolled)
            key_hook = u.SetWindowsHookExW(13, key_callback, None, 0)
            if not key_hook:
                self.post('status', '无法安装全局键盘安全钩子，鼠标控制已禁用')
                return
            mouse_hook = u.SetWindowsHookExW(14, mouse_callback, None, 0)
            if not mouse_hook:
                self.post('status', '真实鼠标活动监控未启动，禁止 AI 自主接管')
                return
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
                active = self.active_io
                if active is not None:
                    try:
                        active.quick_release()
                    except Exception as error:
                        self.emergency_stop('键盘安全钩子失效，无法确认鼠标已释放：' + str(error)[:90])
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
        self.control_state = '安全暂停'
        device.quick_release()
        self.post('phase', '等待目标窗口与有效截图')
        self.post('status', '鼠标已安全暂停；' + str(detail)[:95] + '。窗口和画面恢复后自动继续，按任意键停止')
        while not stop.is_set():
            if not self.keyboard_ready.is_set() or time.monotonic() - self.keyboard_alive_at > max(1., self.watchdog_limit):
                stop.wait(.05)
                continue
            if device.keyboard_activity():
                self.emergency_stop('检测到键盘输入，已停止鼠标控制')
                raise InterruptedError('键盘已停止鼠标控制')
            try:
                region = device.region()
                foreground = region is not None and device.foreground()
            except (OSError, RuntimeError, ValueError) as error:
                self.post('status', '窗口检测正在恢复：' + str(error)[:85] + '；鼠标保持暂停')
                stop.wait(.2)
                continue
            if foreground and self.takeover_allowed():
                try:
                    frame = device.image(region)
                    if device.last_frame_valid and len(frame) == VIS_N:
                        earlier = device.cursor()
                        device.prepare_cursor(region, stop)
                        if device.cursor() != earlier:
                            frame = device.image(region)
                    if not device.last_frame_valid or len(frame) != VIS_N:
                        self.post('status', '正在等待目标窗口产生可验证的新截图；鼠标按键保持释放')
                    else:
                        self.control_state = '控制中'
                        self.post('phase', 'AI 控制中')
                        self.post('status', '目标客户区和画面已恢复，AI 继续控制；按任意键停止')
                        self.control_heartbeat = time.monotonic()
                        self.mouse_monitor_armed.set()
                        return region, frame
                except InterruptedError:
                    raise
                except (OSError, RuntimeError, ValueError) as error:
                    self.post('status', '截图设备正在自动恢复：' + str(error)[:85] + '；鼠标保持暂停')
            stop.wait(max(.05, min(.5, device.last_capture_ms / 1000. if device.last_capture_ms else .2)))
        raise InterruptedError('键盘已停止鼠标控制')

    def control_job(self, hwnd):
        io = None
        ticks = 0
        capture_recovering = False
        last_experience = None
        feedback = Feedback()
        planner = None
        demonstrated_brain = None
        demonstrated = {}
        demonstration_targets = {}
        navigator = TargetNavigator()
        exploration = ExplorationEvidence()
        infer_times = deque(maxlen=96)
        capture_times = deque(maxlen=96)
        frame_times = deque(maxlen=96)
        stage_times = {name: deque(maxlen=96) for name in ('动作', '动作补时', '等待新帧', '反馈', '经验写入', '整轮')}
        last_statistics_at = 0.
        stop = AnyStop(self.control_stop, self.exit_stop)
        try:
            self.load(self.control_stop)
            if not stop.is_set():
                self.post('progress', (25, '初始化 1/4 · 学习引擎已加载'))
                planner = GoalAtlas(self.data_folder)
                self.post('progress', (50, '初始化 2/4 · 规划记忆已加载'))
                self.goal_atlas = planner
                self.post('goal', f'延续 {len(planner.states)} 个历史状态 · 寻找可验证目标')
            if stop.is_set():
                return
            self.post('phase', '检查目标窗口与截图')
            while not stop.is_set() and io is None:
                try:
                    io = WindowsIO(hwnd)
                    io.keyboard_guard = self.keyboard_ready
                    io.input_generation_guard = self.input_generation_current
                except (OSError, RuntimeError, ValueError) as error:
                    self.post('phase', '等待截图设备')
                    self.post('status', '正在恢复鼠标或截图设备：' + str(error)[:90] + '；按任意键停止')
                    stop.wait(.5)
            if stop.is_set():
                return
            self.post('progress', (75, '初始化 3/4 · 截图设备已创建，急停保护已配置'))
            io.human_guard = self.human_idle
            io.user_override = self.user_override
            self.active_io = io
            if not self.takeover_allowed():
                self.post('status', '用户正在操作，已暂停接管；用户空闲后自动继续')
            region, prev_frame = self.await_target(io, stop, '正在检查所选窗口的可操作区域')
            if stop.is_set():
                return
            previous_epoch = io.capture_epoch
            reference_frame = prev_frame
            invalid_frames = 0
            prev_pos = io.cursor()
            prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
            prev_change = 0.
            last_scroll = 0
            last_tick = time.monotonic()
            self.last_checkpoint_step = self.iterations
            self.last_checkpoint_time = time.monotonic()
            self.control_history.clear()
            holdout_mode = False
            holdout_remaining = max(2, math.isqrt(max(1, len(self.brain.memory))))
            self.audit_sum = 0.
            self.audit_samples = 0
            self.start_online()
            if not self.keyboard_ready.is_set():
                self.post('phase', '正在恢复键盘急停监控')
                self.post('status', '键盘急停监控暂未就绪，自动等待恢复；期间绝不发送鼠标动作')
                while not stop.is_set() and not self.keyboard_ready.is_set():
                    if io.keyboard_activity():
                        self.keyboard_stopped_control.set()
                        self.emergency_stop('检测到键盘输入，已停止鼠标控制')
                        break
                    stop.wait(.05)
                if stop.is_set():
                    raise InterruptedError('键盘已停止鼠标控制')
            self.control_heartbeat = time.monotonic()
            self.mouse_monitor_armed.set()
            self.post('progress', (100, '初始化 4/4 · 已验证首帧及控制安全条件'))
            self.control_state = '控制中'
            self.post('phase', 'AI 控制中')
            self.post('status', '无示范时默认仅移动；单独授权后可有限探索标准控件。真实输入可立即中断')
            while not stop.is_set():
                try:
                    if not self.human_idle():
                        raise InterruptedError('用户正在使用鼠标')
                    if not interactive_desktop():
                        raise RuntimeError('Windows 桌面已锁定或会话不再可交互')
                    if io.wgc is None and (self.capture_worker is None or not self.capture_worker.is_alive()):
                        if io.enable_wgc():
                            self.post('capture', 'WGC 截图后端已自动启用，正在同步最新画面')
                    if ticks % max(4, int(math.sqrt(max(1, REPLAY_LIMIT)))) == 0 and (not self.brain.accelerated or getattr(self.brain, 'engine_backend', '') == 'directml'):
                        self.start_acceleration()
                    if self.upgrade_backend(io):
                        self.end_experience(feedback)
                        if stop.is_set():
                            raise InterruptedError('GPU 切换期间收到急停')
                        io.prepare_cursor(region, stop)
                        prev_frame = io.image(region)
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
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
                    dt = max(sys.float_info.epsilon, tick_interval)
                    self.control_interval = dt
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
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                        prev_change = 0.
                        self.post('status', '窗口区域已变化，正在按新位置和尺寸继续控制')
                    io.safe(region, stop)
                    frame = prev_frame
                    preview_now = time.monotonic()
                    if preview_now - self.preview_at >= max(.3, io.last_capture_ms / 1000. * 3):
                        self.preview_at = preview_now
                        self.post('preview', frame)
                    frame_stamp = io.last_capture_stamp
                    frame_epoch = io.capture_epoch
                    capture_ms = io.last_capture_ms
                    if frame_epoch != previous_epoch:
                        io.quick_release()
                        self.end_experience(feedback)
                        prev_frame = frame
                        reference_frame = prev_frame
                        prev_change = 0.
                        previous_epoch = frame_epoch
                    if not io.last_frame_valid:
                        invalid_frames += 1
                        if invalid_frames == 1:
                            io.quick_release()
                            self.end_experience(feedback)
                        if invalid_frames > max(12, int(math.sqrt(max(1, len(self.brain.memory))))):
                            region, prev_frame = self.await_target(io, stop, '连续截图无效，等待截图后端恢复')
                            reference_frame = prev_frame
                            previous_epoch = io.capture_epoch
                            invalid_frames = 0
                            prev_pos = io.cursor()
                            prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                            prev_change = 0.
                            last_tick = time.monotonic()
                            continue
                        self.post('status', '捕获画面不完整或采集源切换中，暂不执行动作')
                        prev_frame = frame
                        reference_frame = prev_frame
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
                    native_targets = io.semantic_targets(region)
                    visual_targets = io.visible_targets(frame)
                    suggested_targets = navigator.targets(native_targets + visual_targets, meta)
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
                    measured_inference = max(infer_times, default=0.) / 1000.
                    measured_capture = max(capture_times, default=0.) / 1000.
                    observed_cycle = max(frame_times, default=io.display_period)
                    self.watchdog_limit = max(time.get_clock_info('monotonic').resolution,
                                               measured_inference + measured_capture + observed_cycle + io.display_period)
                    self.control_heartbeat = time.monotonic()
                    if stop.is_set():
                        raise InterruptedError('控制已停止')
                    if len(history) >= 4 and infer_ms > max(io.display_period * 1000., capture_ms) and infer_ms > history[(3 * (len(history) - 1)) // 4] + 1.5 * (history[(3 * (len(history) - 1)) // 4] - history[(len(history) - 1) // 4]):
                        self.post('status', '模型推理延迟过高，已丢弃过期动作并重新采集窗口')
                        io.release()
                        prev_pos = mouse
                        prev_frame = frame
                        reference_frame = prev_frame
                        prev_dt = dt
                        prev_change = 0.
                        continue
                    if ctrl is None:
                        ctrl = anchor_control(action)
                    if action not in candidates(io.down):
                        raise RuntimeError('模型产生了不允许的动作')
                    progress_probability = (feedback.progress_effects + .5) / (feedback.total + 1.)
                    unexpected_stagnation = math.exp(feedback.stagnant * math.log1p(-progress_probability)) < 1. / (1. + feedback.total)
                    if feedback.loop_count and unexpected_stagnation:
                        safer = [item for item in candidates(io.down) if not ACT[item][3].endswith('+') and not ACT[item][4]]
                        action = explore_action(safer, meta, self.brain.steps, frame, suggested_targets)
                        ctrl = exploratory_control(action, meta)
                    if not isinstance(self.brain, RemoteBrain) or getattr(self.brain, 'steps', 0) < max(1, REPLAY_LIMIT // 2):
                        action, ctrl = navigator.guide(action, ctrl, meta, io.down, self.brain.steps)
                    if len(ctrl) != CTRL_N or not all(math.isfinite(v) for v in ctrl):
                        raise RuntimeError('模型动作参数异常')
                    if demonstrated_brain is not self.brain:
                        with self.brain.save_lock:
                            demonstrated = demonstrated_controls(self.brain.memory)
                        demonstration_targets = demonstrated_target_cells(demonstrated)
                        demonstrated_brain = self.brain
                    permitted = matching_demonstrations(demonstrated, frame, meta)
                    exploratory = (exploration.allowable(frame, meta, io.explorable_controls(mouse, io.down), io.down)
                                   if self.explore_permission.is_set() and self.takeover_permission.is_set() else set())
                    if exploration.pending_release:
                        if io.down.get('l', False):
                            action = BUTTON_ACTIONS[('l', False)]
                            ctrl = anchor_control(action)
                        exploration.pending_release = False
                    elif exploratory and not permitted and not any(io.down.values()):
                        action, ctrl = exploration.choose(action, ctrl, exploratory, feedback)
                    action, ctrl = permitted_autonomous_control(action, ctrl, permitted, io.down, exploratory)
                    if action == BUTTON_ACTIONS[('l', True)] and action in exploratory and action not in permitted:
                        exploration.pending_release = True
                    if not self.takeover_allowed():
                        raise InterruptedError('用户正在使用鼠标或无人值守授权已失效')
                    if not self.mouse_monitor_armed.is_set():
                        raise RuntimeError('安全暂停，重新检查窗口、键盘监控及计算状态')
                    io.safe(region, stop)
                    capture_cycle = max(io.display_period, capture_ms / 1000. + infer_ms / 1000.)
                    duration = max(time.get_clock_info('monotonic').resolution, io.display_period, ctrl[7] * capture_cycle)
                    observed_latency = sum((max(samples, default=0.) for samples in stage_times.values())) / 1000.
                    self.watchdog_limit = max(self.watchdog_limit, duration + io.display_period + observed_latency + capture_cycle)
                    execution_start = time.monotonic()
                    outcome = io.act(normalize_control(ctrl), region, stop, duration)
                    action_finished = time.monotonic()
                    stage_times['动作'].append((action_finished - execution_start) * 1000.)
                    outcome['requested_action'] = action
                    outcome['intended_ctrl'] = normalize_control(ctrl)
                    padding_start = time.monotonic()
                    if self.control_stop.wait(max(0., duration - (padding_start - execution_start))) or stop.is_set():
                        break
                    stage_times['动作补时'].append((time.monotonic() - padding_start) * 1000.)
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
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                        prev_change = 0.
                        continue
                    io.safe(region, stop)
                    fresh_start = time.monotonic()
                    nxt = io.fresh_image(region, action_finished, frame_epoch, stop, execution_start)
                    stage_times['等待新帧'].append((time.monotonic() - fresh_start) * 1000.)
                    capture_times.append(io.last_capture_ms)
                    if nxt is None or io.capture_epoch != frame_epoch or not io.last_frame_valid:
                        io.quick_release()
                        self.end_experience(feedback)
                        previous_epoch = io.capture_epoch
                        prev_frame = io.image(region)
                        reference_frame = prev_frame
                        prev_pos = io.cursor()
                        prev_dt = dt
                        prev_change = 0.
                        capture_recovering = True
                        self.post('status', f'采集自动恢复中：{io.capture_recovery or "动作后画面尚未同步"}；本次经验未写入训练，按任意键停止')
                        continue
                    frame_times.append(tick_interval)
                    new_mouse = io.cursor()
                    feedback_start = time.monotonic()
                    if planner is not None and planner.current_goal is not None:
                        outcome['goal_reached'] = (planner.signature(nxt) == planner.current_goal and planner.signature(frame) != planner.current_goal)
                        outcome['goal_demonstrated'] = planner.current_goal_demonstrated
                    if action in MOTION_ACTIONS and outcome['moved'] > 0.:
                        outcome['demonstration_progress'] = demonstrated_pointer_gain(demonstration_targets, frame, mouse, new_mouse, region)
                    reward, change, advanced = feedback.assess(frame, nxt, reference_frame, outcome, new_mouse, region)
                    exploration.observe(action, frame, nxt, outcome)
                    navigator.observe(reward, outcome)
                    if planner is not None:
                        planner.observe(frame, action, nxt, reward, outcome['efficacy'], advanced)
                    self.audit_sum += reward
                    self.audit_samples += 1
                    actual_dt = max(time.get_clock_info('monotonic').resolution, io.last_capture_stamp - frame_stamp)
                    new_scroll = self.wheel_delta() if self.wheel_hook_ready else outcome['scroll']
                    nmeta = self.create_meta(time.monotonic(), region, new_mouse, mouse, io.keys(), new_scroll, actual_dt, change)
                    stage_times['反馈'].append((time.monotonic() - feedback_start) * 1000.)
                    if holdout_remaining <= 0:
                        holdout_mode = not holdout_mode
                        records_seen = max(1, len(self.brain.memory))
                        correlation_length = max(2, math.isqrt(records_seen))
                        holdout_remaining = correlation_length if holdout_mode else max(correlation_length, math.ceil(records_seen ** .75))
                    holdout_remaining -= 1
                    learn_start = time.monotonic()
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
                    stage_times['经验写入'].append((time.monotonic() - learn_start) * 1000.)
                    stage_times['整轮'].append((time.monotonic() - start) * 1000.)
                    self.control_history.append((outcome['ctrl'][0] * outcome['ctrl'][2], outcome['ctrl'][1] * outcome['ctrl'][2], outcome['ctrl'][6], reward))
                    last_experience = ticks
                    ticks += 1
                    self.iterations += 1
                    if capture_recovering:
                        self.post('status', f'画面采集已恢复（{io.last_frame_backend.upper()}），已重新获得有效训练样本；按任意键停止')
                        capture_recovering = False
                    executed = outcome['ctrl']
                    buttons = io.down.copy()
                    wheel_speed = outcome['scroll'] / max(.001, actual_dt)
                    self.post('control', f'方向 ({executed[0]:+.2f}, {executed[1]:+.2f}) · 移动 {outcome["moved"] / max(.001, duration):.0f} px/s · 左键 {"按下" if buttons["l"] else "释放"} · 右键 {"按下" if buttons["r"] else "释放"} · 中键 {"按下" if buttons["m"] else "释放"} · 滚轮 {wheel_speed:+.0f}/s')
                    statistics_at = time.monotonic()
                    typical_cycle = sorted(frame_times)[len(frame_times) // 2] if frame_times else tick_interval
                    if statistics_at - last_statistics_at >= max(.1, 2. * typical_cycle):
                        last_statistics_at = statistics_at
                        def p95(samples):
                            ordered = sorted(samples)
                            return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * .95))] if ordered else 0.
                        fps = len(frame_times) / max(.001, sum(frame_times))
                        perf = self.brain.latest_perf if isinstance(self.brain, RemoteBrain) else {}
                        gpu_training = f' · 在线复盘 {perf.get("batches", 0)} 批 · 训练 {perf["training_samples_per_second"]:.1f}样本/s · 批量 {perf["batch_size"]} · GPU传输 {perf["transfer_ms"]:.1f}ms' if perf and self.brain.accelerated else (f' · 在线复盘 {self.brain.online_batches} 批' if isinstance(self.brain, LiteBrain) else '')
                        if isinstance(self.brain, RemoteBrain):
                            gpu_training += ' · 进程间共享双帧' if self.brain.shared_frames is not None else ' · 标准进程传输'
                            if self.brain.online_train_deferrals:
                                gpu_training += f' · 实时推理优先跳过训练 {self.brain.online_train_deferrals} 次'
                        if perf and 'gpu_memory_total_gb' in perf:
                            gpu_training += f' · 显存 {perf["gpu_memory_used_gb"]:.2f}/{perf["gpu_memory_total_gb"]:.2f}GB'
                        if perf and perf.get('cuda_model_validated'):
                            gpu_training += f' · CUDA参数更新 {perf.get("cuda_optimizer_steps", 0)} 次'
                            self.post('gpu_state', self.brain.label + (' · CUDA训练已实际执行' if perf.get('cuda_optimizer_steps', 0) else ' · CUDA模型前后向验证通过，正在等待训练数据') + f' · 累计训练 {perf.get("training_examples", 0)} 样本')
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
                        segments = ' · '.join(f'{label}P95 {p95(samples):.0f}ms' for label, samples in stage_times.items())
                        self.post('fps', f'控制 FPS：{fps:.2f}')
                        self.post('capture', f'{VIS_W}×{VIS_H} 双视野 · {io.last_frame_backend or "未定"} · 实际采集 {io.last_capture_ms:.0f}ms · {fps:.2f}FPS · 目标与推理P95 {p95(infer_times):.0f}ms · ' + segments + (f' · 回退 {failures} 次' if failures else ''))
                        archive = getattr(self.brain, 'archive', None)
                        archived = archive.kept if archive is not None else perf.get('archive_count', '后台保存')
                        self.post('goal', planner.description if planner is not None else '目标规划未启动')
                        archival_health = (f' · 归档排队 {archive.pending.qsize()} · 溢出未归档 {archive.dropped} · 写盘P95 {p95(archive.write_ms):.1f}ms · 排队P95 {p95(archive.queue_ms):.1f}ms' + (' · 归档异常 ' + archive.error[:65] if archive.error else '')) if archive is not None else ''
                        self.post('stats', f'短期经验 {len(self.brain.memory)} · 长期经验 {archived} · 操作 {self.iterations} · 可控进展 {feedback.progress_effects}/{feedback.total} · 示范目标画面匹配 {feedback.demonstrated_goal_matches} · 示范指针接近 {feedback.demonstrated_pointer_advances} · 试探点击 {exploration.attempts} 次 / 可观测画面变化 {exploration.effects} 次 · 重复可归因 {feedback.causal_evidence} · 循环 {feedback.loop_count} · 预测误差 {prediction:.3f} · 因果证据强度 {causal:.2f} · 被动基线 {feedback.passive_count} 次 · 受阻 {feedback.blocks}（均非任务成功率）' + gpu_training + archival_health)
                    with self.brain.save_lock:
                        saved_count = len(self.brain.memory)
                    pending = self.iterations - self.last_checkpoint_step
                    minimum_samples = max(8, int(math.sqrt(max(1, saved_count))))
                    minimum_seconds = max(5., self.last_checkpoint_duration * 12., math.log2(2. + saved_count))
                    if pending >= minimum_samples and time.monotonic() - self.last_checkpoint_time >= minimum_seconds:
                        self.schedule_checkpoint()
                    reference_frame = frame
                    prev_frame = nxt
                    prev_pos = new_mouse
                    prev_change = change
                    prev_dt = actual_dt
                    last_scroll = outcome['scroll']
                except InterruptedError as interrupted:
                    if stop.is_set():
                        raise
                    if io.keyboard_activity() or self.keyboard_stopped_control.is_set():
                        self.emergency_stop('检测到键盘输入，已停止鼠标控制')
                        raise InterruptedError('键盘已停止鼠标控制') from interrupted
                    io.quick_release()
                    self.end_experience(feedback)
                    region, prev_frame = self.await_target(io, stop, str(interrupted))
                    reference_frame = prev_frame
                    previous_epoch = io.capture_epoch
                    invalid_frames = 0
                    prev_pos = io.cursor()
                    prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                    prev_change = 0.
                    last_tick = time.monotonic()
                except (OSError, RuntimeError, ValueError, TimeoutError) as failure:
                    if stop.is_set():
                        raise InterruptedError('键盘已停止鼠标控制')
                    io.quick_release()
                    self.end_experience(feedback)
                    stop.wait(.2)
                    region, prev_frame = self.await_target(io, stop, failure)
                    reference_frame = prev_frame
                    previous_epoch = io.capture_epoch
                    invalid_frames = 0
                    prev_pos = io.cursor()
                    prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                    prev_change = 0.
                    last_tick = time.monotonic()
            if self.control_stop.is_set():
                self.post('status', '用户已接回鼠标，正在自动返回观察学习模式')
        except InterruptedError as interrupted:
            if self.keyboard_stopped_control.is_set() or '键盘' in str(interrupted) or '按键' in str(interrupted):
                self.keyboard_stopped_control.set()
                self.control_stop.set()
            self.post('status', '鼠标控制已安全中断，所有模拟鼠标按键已请求释放')
        except RuntimeError as ex:
            self.post('error', '控制发生无法自动恢复的问题：' + str(ex)[:125])
        except Exception as ex:
            self.post('error', '控制发生无法自动恢复的问题：' + str(ex)[:125])
        finally:
            self.mouse_monitor_armed.clear()
            self.control_heartbeat = 0.
            self.control_interval = 0.
            self.post('fps', '控制 FPS：已停止')
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
                    current_metrics = {'frames': self.audit_samples, 'mean': quality, 'timestamp': time.time(), 'efficacy': feedback.efficacy_total / max(1, feedback.total), 'progress_rate': feedback.progress_effects / max(1, feedback.total), 'demonstrated_goal_matches': feedback.demonstrated_goal_matches, 'demonstrated_pointer_advances': feedback.demonstrated_pointer_advances, 'repetition_rate': feedback.repeats / max(1, feedback.total), 'blocked_rate': feedback.blocks / max(1, feedback.total), 'causal_repeats': feedback.causal_evidence, 'backend': self.brain.label if self.brain is not None else '未知'}
                    if frame_times:
                        current_metrics['control_fps'] = len(frame_times) / max(sys.float_info.epsilon, sum(frame_times))
                    timed = {'目标与推理': infer_times, '截图耗时': capture_times}
                    timed.update(stage_times)
                    current_metrics['latency_p95_ms'] = {label: sorted(values)[int(.95 * (len(values) - 1))] for label, values in timed.items() if values}
                    archive = getattr(self.brain, 'archive', None)
                    if archive is not None:
                        current_metrics['archive_overflow'] = archive.dropped
                        current_metrics['archive_write_p95_ms'] = sorted(archive.write_ms)[int(.95 * (len(archive.write_ms) - 1))] if archive.write_ms else None
                        current_metrics['archive_queue_p95_ms'] = sorted(archive.queue_ms)[int(.95 * (len(archive.queue_ms) - 1))] if archive.queue_ms else None
                    comparison = ''
                    pending_comparison = False
                    history = audit.get('history', []) if isinstance(audit, dict) else []
                    history = history[-31:] if isinstance(history, list) else []
                    if previous_sleep and isinstance(previous, dict) and previous.get('frames', 0) > 0:
                        keys = [('mean', '平均反馈'), ('efficacy', '动作执行率'), ('progress_rate', '可控进展率'), ('repetition_rate', '重复率'), ('blocked_rate', '受阻率')]
                        differences = [f'{label} {previous[key]:+.3f}→{current_metrics[key]:+.3f}' for key, label in keys if key in previous]
                        sufficient = min(self.audit_samples, previous.get('frames', 0)) >= max(8, math.ceil(math.sqrt(self.audit_samples + previous.get('frames', 0))))
                        if sufficient:
                            indicators = [current_metrics['progress_rate'] - previous.get('progress_rate', 0.), previous.get('repetition_rate', 0.) - current_metrics['repetition_rate'], previous.get('blocked_rate', 0.) - current_metrics['blocked_rate']]
                            direction = '可观测指标倾向改善' if sum(delta > 0. for delta in indicators) > sum(delta < 0. for delta in indicators) else '尚未发现一致的行为改善'
                            comparison = '；睡眠前后同环境对比（' + direction + '）：' + '、'.join(differences) + '（不代表任务成功）'
                            history.append({'before': previous, 'after': current_metrics, 'trend': direction})
                        else:
                            pending_comparison = True
                            comparison = '；睡眠后样本尚不足以比较行为变化，继续积累经验'
                    self.data_folder.mkdir(parents=True, exist_ok=True)
                    save_json(path, {'last': previous if pending_comparison else current_metrics, 'pending_sleep': pending_comparison, 'history': history})
                    if comparison:
                        self.post('status', '控制已结束' + comparison)
                except (OSError, ValueError, TypeError) as ex:
                    self.post('error', '表现记录未保存：' + str(ex)[:110])
            if self.goal_atlas is planner:
                self.goal_atlas = None
            self.post('task_result', '键盘停止' if self.control_stop.is_set() else '安全结束')
            self.post('done', 'control')

    def close(self):
        if self.mode == 'closed':
            return
        self.mode = 'closed'
        self.start_queued = None
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
        self.observer_stop.set()
        self.exit_stop.set()
        self.release_signal.set()
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
        if self.shutdown_worker is None and not main_busy:
            def cleanup():
                if self.brain is not None:
                    try:
                        self.brain.close()
                    except Exception:
                        pass
            self.shutdown_worker = threading.Thread(target=cleanup, daemon=True)
            self.shutdown_worker.start()
        busy |= self.shutdown_worker is not None and self.shutdown_worker.is_alive()
        tracked = (self.worker, self.control_worker, self.saver, self.online_worker, self.acceleration_cleanup, self.acceleration_thread, self.capture_worker, self.key_thread, self.safety_thread, self.exit_backup, self.release_worker, self.shutdown_worker, self.initializer)
        pending = sum(task is not None and task.is_alive() for task in tracked)
        finished = sum(task is not None and not task.is_alive() for task in tracked)
        ratio = finished / max(1, finished + pending)
        self.set_progress(min(99., max(self.progress_value.get(), 99. * ratio)), '正在释放资源并保存恢复点')
        if busy and elapsed < deadline:
            self.root.after(100, self.finish_close)
            return
        if busy:
            self.status.set('已达到退出等待上限，强制结束仍未响应的后台任务；恢复数据优先从最新检查点加载')
            threading.Thread(target=stop_all_processes, daemon=True).start()
        elif self.exit_backup_error is not None:
            self.status.set('紧急备份未完成：' + self.exit_backup_error)
        if not busy and self.exit_backup_error is None:
            self.set_progress(100, '退出完成')
        else:
            self.set_progress(self.progress_value.get(), '退出结束 · 未确认所有数据已保存', 'failed')
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
