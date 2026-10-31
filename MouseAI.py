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
import traceback
import gc
import tempfile
from pathlib import Path
from collections import deque, Counter
from functools import lru_cache
import tkinter as tk
from tkinter import ttk, filedialog, font as tkfont

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
KEYBOARD_HEARTBEAT_TIMEOUT = 1.
BUTTON_STALE_TIMEOUT = 12.
CTRL_N = 8
META_N = 24
AI_INPUT_MARK = int.from_bytes(os.urandom(ctypes.sizeof(ctypes.c_size_t)), 'little') | 1

def own_mouse_event(flags, extra):
    return bool(int(flags) & 1) and int(extra) == AI_INPUT_MARK
CHILD_PROCESSES = set()
CHILD_LOCK = threading.RLock()
FILE_LOCKS = {}
FILE_LOCKS_GUARD = threading.Lock()


def file_write_lock(path):
    key = str(Path(path).absolute())
    with FILE_LOCKS_GUARD:
        lock = FILE_LOCKS.get(key)
        if lock is None:
            lock = threading.RLock()
            FILE_LOCKS[key] = lock
    return lock


def unique_temp_path(path):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + '.', suffix='.tmp', dir=str(path.parent))
    os.close(descriptor)
    return Path(temporary)



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
REPLAY_MAGIC = b'MOUSEA13'
REPLAY_PACK = struct.Struct('<BBf?ff?BII' + 'f' * (META_N * 2 + CTRL_N * 2))
CAPTURE_SOURCES = {'unknown': 0, 'wgc': 1, 'dxcam': 2, 'gdi': 3}
CAPTURE_VERIFIED = 0x80
DEMONSTRATION_FLAG = 0x80
SAFE_NAVIGATION_LABELS = frozenset(('back', 'go back', 'next', 'previous', 'forward', 'home', 'menu',
                                    'more', 'more options', 'browse', 'explore', 'view', 'view details',
                                    'details', 'read more', 'next page', 'previous page', 'go home',
                                    'show more', 'show less', 'expand', 'collapse', 'help',
                                    '返回', '后退', '前进', '上一页', '下一页', '首页', '菜单', '更多',
                                    '查看', '查看详情', '浏览', '展开', '收起', '帮助', '继续浏览'))
def semantic_action(label, role='button'):
    name = ' '.join(str(label).casefold().split())
    if not name:
        return 'unknown'
    if role not in ('button', 'link', 'tab', 'menu'):
        return 'unknown'
    if name in SAFE_NAVIGATION_LABELS or re.fullmatch(r'(next|previous|back) (page|tab|item|result)s?', name):
        return 'navigation'
    return 'unknown'


def safe_demonstrated_element(info, position, allow_unknown=False):
    if info is None:
        return False
    label, role, bounds = info
    name = ' '.join(str(label).casefold().split())
    if not name or role not in ('button', 'link', 'tab', 'menu') or bounds is None:
        return False
    action = semantic_action(name, role)
    if action != 'navigation' and not allow_unknown:
        return False
    try:
        left, top, right, bottom = bounds
        px, py = position
        return left < right and top < bottom and left <= px < right and top <= py < bottom
    except (ValueError, TypeError, OverflowError):
        return False


def experience_header(row):
    ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed, efficacy, reserved = row[:13]
    encoded = executed | (DEMONSTRATION_FLAG if len(row) > 13 and row[13] else 0)
    return REPLAY_PACK.pack(action, encoded, reward, done, dt, efficacy, reserved,
                            int(row[14]) if len(row) > 14 else 0,
                            encode_action_mask(row[15] if len(row) > 15 else SAFE_FUTURE_MASK),
                            encode_action_mask(row[16] if len(row) > 16 else SAFE_FUTURE_MASK),
                            *meta, *nmeta, *ctrl, *intended)


def experience_digest(records):
    digest = hashlib.blake2s(digest_size=16)
    digest.update(struct.pack('<Q', len(records)))
    for row in records:
        digest.update(experience_header(row))
        digest.update(row[0])
        digest.update(row[3])
    return digest.digest()


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


def rebalance_replay_memory(brain, pressure):
    pressure = max(0., min(1., float(pressure)))
    budget = max(1, min(REPLAY_LIMIT, max(8, int(REPLAY_LIMIT * (1. - pressure)))))
    setter = getattr(brain, 'set_replay_limit', None)
    if setter is not None:
        setter(budget)
        return
    lock = getattr(brain, 'save_lock', None)
    if lock is None:
        return
    with lock:
        brain.replay_runtime_limit = budget
        while len(brain.memory) > budget:
            brain.memory.popleft()


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
    ram_budget = min(1024 * 1024 * 1024, max(64 * 1024 * 1024, free // 16)) if free else 128 * 1024 * 1024
    available = max(1, min(ram_budget // sample_size, free // max(1, sample_size * copies))) if free else max(1, ram_budget // sample_size)
    try:
        inherited = int(os.environ.get('MOUSEAI_REPLAY_CAPACITY', '0'))
        return min(available, inherited) if inherited > 0 else available
    except (TypeError, ValueError, OverflowError):
        return available

REPLAY_LIMIT = replay_capacity()

def world_model_evidence_floor(parameters, worlds, capacity=None):
    available = REPLAY_LIMIT if capacity is None else max(1, int(capacity))
    complexity = math.log2(2. + max(0, int(parameters)))
    required = math.ceil(complexity * (2. + math.sqrt(1. + max(0, int(worlds)))))
    return max(1, min(required, max(1, available // 3)))

REPLAY_FILE_RECORD_LIMIT = 131072
MIN_ARCHIVE_RESERVE_BYTES = 256 * 1024 * 1024
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
ALL_ACTION_MASK = (1 << ACT_N) - 1
SAFE_FUTURE_MASK = ALL_ACTION_MASK


def encode_action_mask(actions=None):
    if actions is None:
        return ALL_ACTION_MASK
    if isinstance(actions, int) and not isinstance(actions, bool):
        mask = actions & ALL_ACTION_MASK
    else:
        mask = sum(1 << int(action) for action in set(actions) if 0 <= int(action) < ACT_N)
    return mask | (1 << IDLE_ACTION)


def future_action_candidates(meta, action_mask=SAFE_FUTURE_MASK):
    held = {'l': meta[9] > .5, 'r': meta[10] > .5, 'm': meta[11] > .5}
    mask = encode_action_mask(action_mask)
    for button in ('l', 'r', 'm'):
        if held[button]:
            mask |= 1 << BUTTON_ACTIONS[(button, False)]
    return [action for action in candidates(held) if mask & (1 << action)]


def experience_identity(row):
    digest = hashlib.blake2s(digest_size=16)
    digest.update(experience_header((*row[:6], False, *row[7:])))
    digest.update(row[0])
    digest.update(row[3])
    return digest.digest()



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
                    (device.keyboard_heartbeat_guard is not None and not device.keyboard_heartbeat_guard()) or
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



def completed_click_index(samples, old_held, held):
    if any(old_held.values()) or any(held.values()):
        return None
    press = release = None
    for index, sample in enumerate(samples):
        if sample[4]:
            return None
        for switch in sample[3]:
            if switch == 'l+' and press is None and release is None:
                press = index
            elif switch == 'l-' and press is not None and release is None:
                release = index
            else:
                return None
    if press is None or release is None:
        return None
    anchor = samples[press][6]
    if any(math.dist(anchor, sample[6]) > 6. for sample in samples[press:release + 1]):
        return None
    return press


def completed_deferred_click(pending, samples, held, cursor, region, epoch, stamp):
    if (pending is None or region != pending['region'] or epoch != pending['epoch'] or
            stamp <= pending['frame_at'] or stamp - pending['pressed_at'] > 2. or any(held.values())):
        return False
    switches = [switch for sample in samples for switch in sample[3]]
    if switches != ['l-'] or any(sample[4] for sample in samples):
        return False
    anchor = pending['position']
    return (math.dist(anchor, cursor) <= 6. and
            all(math.dist(anchor, sample[6]) <= 6. for sample in samples))


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


def permitted_autonomous_control(action, ctrl):
    if not 0 <= int(action) < ACT_N:
        action = IDLE_ACTION
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
            self.pending_release = True
            return press, anchor_control(press)
        if action == press:
            self.pending_release = True
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
            key = (demonstration_signature(row[0]), round(meta[4] * VIS_W / CELL_W), round(meta[5] * VIS_H / CELL_H))
            index.setdefault(key, set()).add(action)
        except (ValueError, TypeError, OverflowError):
            continue
    return index


def matching_demonstrations(index, frame, meta):
    if not index:
        return set()
    signature = demonstration_signature(frame)
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


def visual_target_pointer_gain(target, before, after, region, meta):
    if target is None or before == after:
        return 0.
    x, y, w, h = region
    if w <= 0 or h <= 0:
        return 0.
    tx, ty, quality = target
    if not (math.isfinite(tx) and math.isfinite(ty) and math.isfinite(quality)):
        return 0.
    start_x, start_y = (before[0] - x) / w, (before[1] - y) / h
    finish_x, finish_y = (after[0] - x) / w, (after[1] - y) / h
    original = math.hypot(*pointer_offset(tx - start_x, ty - start_y, meta))
    remaining = math.hypot(*pointer_offset(tx - finish_x, ty - finish_y, meta))
    if original <= pointer_pixel_radius(meta) * 1.5 or remaining >= original:
        return 0.
    movement = math.hypot(*pointer_offset(finish_x - start_x, finish_y - start_y, meta))
    return min(1., (original - remaining) / max(pointer_pixel_radius(meta), movement)) * min(1., max(0., quality))


def demonstrated_pointer_gain(targets, frame, before, after, region):
    if not targets or before == after:
        return 0.
    x, y, w, h = region
    if w <= 0 or h <= 0:
        return 0.
    signature = demonstration_signature(frame)
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
        return None
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
        if row[12] or (len(row) > 13 and row[13]):
            continue
        exposure += max(sys.float_info.epsilon, float(row[7]))
        endings += bool(row[6])
    return max(.02, endings / exposure) if exposure > 0. else .02


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
        if row[12] or (offset and (final[6] or row[0] != final[3] or row[1][-2:] != final[4][-2:] or (len(row) > 13 and row[13]) != (len(first) > 13 and first[13]))):
            break
        total += discount * row[5]
        duration += row[7]
        discount *= temporal_discount(row[7], discount_rate)
        final = row
        if row[6]:
            break
    next_mask = final[16] if len(final) > 16 else SAFE_FUTURE_MASK
    return (first[0], first[1], first[2], final[3], final[4], total, final[6], duration, *first[8:16], next_mask)


def quarantine(path):
    if path.exists():
        try:
            os.replace(path, path.with_name(path.name + '.damaged'))
        except OSError:
            pass

_IMAGE_NUMPY = None
_IMAGE_NUMPY_CHECKED = False


def enable_numpy_acceleration():
    global _IMAGE_NUMPY, _IMAGE_NUMPY_CHECKED
    module = importlib.import_module('numpy')
    _IMAGE_NUMPY = module
    _IMAGE_NUMPY_CHECKED = True
    return module


@lru_cache(maxsize=16)
def coarse_image_cells(image):
    global _IMAGE_NUMPY, _IMAGE_NUMPY_CHECKED
    if len(image) != VIS_N:
        raise ValueError('状态识别画面维度不匹配')
    if not _IMAGE_NUMPY_CHECKED:
        _IMAGE_NUMPY_CHECKED = True
        try:
            enable_numpy_acceleration()
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


def local_signature(image):
    cells = coarse_image_cells(image)
    return hashlib.blake2s(bytes(cells[CELLS_PER_VIEW * CHANNELS:]), digest_size=8).digest()


def element_scene_signature(image):
    return demonstration_signature(image) + session_signature(image)


@lru_cache(maxsize=32)
def demonstration_signature(image):
    cells = coarse_image_cells(image)
    columns, rows = VIS_W // CELL_W, VIS_H // CELL_H
    luminance = []
    for gy in range(8):
        y0, y1 = gy * rows // 8, (gy + 1) * rows // 8
        for gx in range(8):
            x0, x1 = gx * columns // 8, (gx + 1) * columns // 8
            total = 0
            count = 0
            for cy in range(y0, y1):
                for cx in range(x0, x1):
                    offset = (cy * columns + cx) * CHANNELS
                    total += 77 * cells[offset] + 150 * cells[offset + 1] + 29 * cells[offset + 2]
                    count += 1
            luminance.append(total // max(1, 256 * count))
    center = sorted(luminance)[len(luminance) // 2]
    bits = sum((1 << i) for i, value in enumerate(luminance) if value > center)
    first_view = cells[:CELLS_PER_VIEW * CHANNELS]
    mean_colors = [sum(first_view[channel::CHANNELS]) // CELLS_PER_VIEW for channel in range(CHANNELS)]
    mean_level = sum(luminance) // len(luminance)
    color_key = bytes((min(15, mean_level // 16),
                       min(15, max(0, (mean_colors[0] - mean_colors[1] + 272) // 32)),
                       min(15, max(0, (mean_colors[2] - mean_colors[1] + 272) // 32))))
    return bits.to_bytes(8, 'little') + color_key


class TargetNavigator:
    def __init__(self):
        self.visits = Counter()
        self.outcomes = {}
        self.focus = None
        self.focus_key = None
        self.release_pending = False
        self.last_intent = None
        self.pending_press_effect = 0.
        self.total = 0

    @staticmethod
    def identifier(x, y, scene=None):
        return (scene, round(float(x) * VIS_W / max(1, CELL_W)), round(float(y) * VIS_H / max(1, CELL_H)))

    def targets(self, points, meta, scene=None):
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
            key = self.identifier(x, y, scene)
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
        self.focus_key = self.identifier(*self.focus[:2], scene=scene)
        return tuple(point for _, point in ordered)

    def guide(self, action, control, meta, held, steps):
        if self.release_pending and held.get('l'):
            self.release_pending = False
            if self.last_intent is None:
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
            self.pending_press_effect = 0.
            return
        switches = tuple(outcome.get('switches') or ())
        effect = max(0., float(reward)) * max(0., min(1., float(outcome.get('efficacy', 1.))))
        if outcome.get('blocked'):
            effect = 0.
        if 'l+' in switches:
            self.pending_press_effect = max(self.pending_press_effect, effect)
            return
        if 'l-' in switches:
            effect = max(effect, self.pending_press_effect)
            self.pending_press_effect = 0.
        elif switches:
            self.pending_press_effect = 0.
        if 'l-' in switches or outcome.get('scroll') or switches:
            tries = self.visits[key]
            good, count = self.outcomes.get(key, (0., 0))
            count += 1
            good += (effect - good) / count
            self.outcomes[key] = (good, count)
            self.visits[key] = max(tries, count)
            self.last_intent = None
            self.focus = None
            self.focus_key = None
        limit = max(32, REPLAY_LIMIT * 2)
        if len(self.visits) > limit:
            victim_count = max(1, len(self.visits) // 8)
            for victim in sorted(self.visits, key=self.visits.get)[:victim_count]:
                if victim not in (self.focus_key, self.last_intent):
                    self.visits.pop(victim, None)
                    self.outcomes.pop(victim, None)


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
        self.verified_goal_matches = 0
        self.pending_goal = None
        self.demonstrated_goal_matches = 0
        self.demonstrated_pointer_advances = 0
        self.visual_target_advances = 0
        self.efficacy_total = 0.
        self.stagnant = 0
        self.loop_count = 0
        self.causal_total = 0.
        self.passive_context = {}
        self.action_context = {}
        self.state_value = {}
        self.causal_evidence = 0
        self.previous_passive = False
        self.pending_buttons = {}
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
        self.pending_goal = None
        self.pending_buttons.clear()

    def difference(self, left, right, view=0):
        if len(left) != VIS_N or len(right) != VIS_N or view not in (0, 1):
            raise ValueError('画面反馈维度不匹配')
        if self.numpy is None and _IMAGE_NUMPY is not None:
            self.numpy = _IMAGE_NUMPY
        pixels = CHANNELS * PIXELS
        offset = view * pixels
        if self.numpy is not None:
            np = self.numpy
            a = np.frombuffer(left, dtype=np.uint8, count=pixels, offset=offset).astype(np.int16)
            b = np.frombuffer(right, dtype=np.uint8, count=pixels, offset=offset).astype(np.int16)
            return float(np.abs(a - b).mean()) / 255.
        return sum(abs(a - b) for a, b in zip(left[offset:offset + pixels], right[offset:offset + pixels])) / (pixels * 255.)

    def assess(self, old, new, previous, outcome, pointer, region):
        local_aligned = bool(outcome.get('local_aligned')) and float(outcome.get('moved', 0.)) < 1.
        dist = self.difference(old, new)
        bg = self.difference(previous, old) if previous is not None else dist
        if local_aligned:
            dist = max(dist, self.difference(old, new, 1))
            if previous is not None:
                bg = max(bg, self.difference(previous, old, 1))
        if self.previous_passive:
            self.background_count += 1
            count = self.background_count
            old_background = self.background if self.background is not None else 0.
            delta = bg - old_background
            self.background = old_background + delta / count
            self.variance += (delta * (bg - self.background) - self.variance) / count
        count = max(1, self.background_count)
        changed = bool(outcome['changed'])
        self.previous_passive = previous is not None and not changed and not outcome['blocked']
        if not changed and not outcome['blocked']:
            self.passive_count += 1
            d = dist - self.passive_average
            self.passive_average += d / self.passive_count
            self.passive_variance += (d * (dist - self.passive_average) - self.passive_variance) / self.passive_count

        signature = session_signature(new)
        old_signature = session_signature(old)
        if self.pending_goal is not None:
            if old_signature == signature == self.pending_goal and not outcome['blocked']:
                self.verified_goal_matches += 1
            self.pending_goal = None
        context = old_signature
        idle_mean, idle_var, idle_visits = self.passive_context.get(context, (0., 0., 0))
        ambient = max((self.background or 0.) + math.sqrt(max(0., self.variance)),
                      self.passive_average + math.sqrt(max(0., self.passive_variance)),
                      idle_mean + math.sqrt(max(0., idle_var)))
        pixel_resolution = 1. / (CHANNELS * PIXELS * 255.)
        impact = max(0., dist - ambient)
        noise_error = math.sqrt(max(0., self.variance) / count)
        scene_changed = old_signature != signature or (local_aligned and local_signature(old) != local_signature(new))
        signal = (previous is not None and changed and scene_changed and
                  impact > max(pixel_resolution, noise_error))
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
        switches = tuple(outcome.get('switches') or ())
        if signal:
            for button in self.pending_buttons:
                self.pending_buttons[button] = True
        completed_without_effect = False
        for switch in switches:
            if switch in ('l+', 'r+', 'm+'):
                self.pending_buttons[switch[0]] = bool(signal)
            elif switch in ('l-', 'r-', 'm-'):
                completed_without_effect |= not (self.pending_buttons.pop(switch[0], False) or signal)
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
        visual_gain = max(0., min(1., float(outcome.get('visual_target_progress', 0.))))
        visual_gain *= float(action in MOTION_ACTIONS and outcome.get('moved', 0.) > 0. and not outcome['blocked'])
        intrinsic_gain = (causal_strength + discovery * persistence + state_advantage * attributable) * novelty * ((1. + confidence) / 2.)
        intrinsic_gain += .15 * visual_gain / math.sqrt(1. + transition_visits)
        task_gain = goal_gain + pointer_gain
        capture_confidence = max(0., min(1., float(outcome.get('capture_confidence', 1.))))
        gain = (intrinsic_gain + task_gain) * efficacy * capture_confidence * float(not loop)
        if signal:
            n = prior_count + 1
            d = impact - prior_effect
            mean = prior_effect + d / n
            variance = prior_variance + (d * (impact - mean) - prior_variance) / n
            self.action_context[(context, action)] = (mean, max(0., variance), n)
        attempted = float(action != IDLE_ACTION and not outcome.get('pending_scroll'))
        moved_successfully = bool(action in MOTION_ACTIONS and outcome.get('moved', 0.) > 0.
                                  and efficacy >= .5 and not outcome['blocked'])
        ineffective = float(not signal and not pointer_gain and not moved_successfully and
                            (not switches or completed_without_effect))
        failure = attempted * (1. - efficacy)
        failure += float(bool(outcome['blocked']))
        failure += ineffective * repetition * attempted
        failure += repeated_fraction * float(loop)
        failure += attempted * repetition * repeated_fraction * float(
            (ineffective and new_seen >= old_seen) or (loop and not pointer_gain))
        reward = math.tanh(gain - failure * capture_confidence)
        progress = bool(reward > 0. and efficacy > 0. and not loop and
                        ((signal and scene_changed and (reached or (prior_count > 1 and causal_strength > 0.)))
                         or ((pointer_gain > 0. or visual_gain > 0.) and moved_successfully)))
        if reached and efficacy > 0.:
            self.pending_goal = signature
        self.demonstrated_goal_matches += int(reached and efficacy > 0.)
        self.demonstrated_pointer_advances += int(pointer_gain > 0. and not loop)
        self.visual_target_advances += int(visual_gain > 0. and not loop)
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


class ReplayBuffer(deque):
    pass


def stored_experience_digest(records):
    return getattr(records, 'source_digest', None) or experience_digest(records)


def replay_extension(previous, current):
    if not previous or not current:
        return None
    recent = list(current)
    pattern = [experience_identity(row) for row in recent]
    prefix = [0] * len(pattern)
    for index in range(1, len(pattern)):
        length = prefix[index - 1]
        while length and pattern[index] != pattern[length]:
            length = prefix[length - 1]
        if pattern[index] == pattern[length]:
            length += 1
        prefix[index] = length
    matched = 0
    for row in previous:
        identity = experience_identity(row)
        while matched and (matched == len(pattern) or identity != pattern[matched]):
            matched = prefix[matched - 1]
        if identity == pattern[matched]:
            matched += 1
    return recent[matched:] if matched else None


def read_replay(folder, slot):
    path = folder / f'experience.{slot}.gz'
    records = ReplayBuffer(maxlen=REPLAY_LIMIT)
    try:
        digest = hashlib.sha256()
        full_experience_digest = hashlib.blake2s(digest_size=16)
        with gzip.open(path, 'rb') as f:
            head = f.read(len(REPLAY_MAGIC) + 12)
            if len(head) != len(REPLAY_MAGIC) + 12 or head[:len(REPLAY_MAGIC)] != REPLAY_MAGIC:
                raise ValueError('经验文件版本错误')
            digest.update(head)
            count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
            if count > REPLAY_FILE_RECORD_LIMIT or generation < 1:
                raise ValueError('经验标头异常')
            records.source_count = count
            full_experience_digest.update(struct.pack('<Q', count))
            previous_next = None
            for _ in range(count):
                raw = f.read(REPLAY_PACK.size)
                if len(raw) != REPLAY_PACK.size:
                    raise ValueError('经验数据不完整')
                digest.update(raw)
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
                nxt = f.read(VIS_N)
                if len(ob) != VIS_N or len(nxt) != VIS_N:
                    raise ValueError('经验画面数据不完整')
                digest.update(nxt)
                values = REPLAY_PACK.unpack(raw)
                action, executed_action, reward, done, dt, efficacy, reserved, capture_code, action_mask, next_mask = values[:10]
                numeric = values[10:]
                demonstration = bool(executed_action & DEMONSTRATION_FLAG)
                executed_action &= ~DEMONSTRATION_FLAG
                if (action >= ACT_N or executed_action >= ACT_N or not math.isfinite(reward) or
                        not math.isfinite(dt) or dt <= 0. or not math.isfinite(efficacy) or
                        not 0. <= efficacy <= 1. or not all(math.isfinite(v) for v in numeric) or
                        action_mask != encode_action_mask(action_mask) or next_mask != encode_action_mask(next_mask)):
                    raise ValueError('经验数值无效')
                meta = tuple(numeric[:META_N])
                nmeta = tuple(numeric[META_N:META_N * 2])
                ctrl = tuple(numeric[META_N * 2:META_N * 2 + CTRL_N])
                intended = tuple(numeric[META_N * 2 + CTRL_N:])
                full_experience_digest.update(raw)
                full_experience_digest.update(ob)
                full_experience_digest.update(nxt)
                records.append((ob, meta, action, nxt, nmeta, float(reward), bool(done), float(dt), ctrl, intended, executed_action, float(efficacy), bool(reserved), demonstration, int(capture_code), int(action_mask), int(next_mask)))
                previous_next = nxt
            if f.read(32) != digest.digest() or f.read(1):
                raise ValueError('经验校验失败')
        records.source_digest = full_experience_digest.digest()
        records.truncated = count > len(records)
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
            if len(head) == len(REPLAY_MAGIC) + 12 and head[:len(REPLAY_MAGIC)] == REPLAY_MAGIC:
                count, generation = struct.unpack('<IQ', head[len(REPLAY_MAGIC):])
                if 0 <= count <= REPLAY_FILE_RECORD_LIMIT and generation > 0:
                    headers.append((generation, slot))
        except (OSError, EOFError, ValueError, struct.error, zlib.error):
            continue
    for generation, slot in sorted(headers, key=lambda row: (row[0], row[1] == 'recovery'), reverse=True):
        record = read_replay(folder, slot)
        if record is not None and record[1] == generation:
            yield generation, slot, record[0]


def newest_replay(folder):
    return next(replay_sources(folder), None)


def discard_recovery(folder, generation, records=None):
    path = folder / 'experience.recovery.gz'
    if records is None:
        return
    recovered = read_replay(folder, 'recovery')
    if recovered is None or recovered[1] > generation:
        return
    saved = list(records)
    backup = list(recovered[0])
    if not backup or not saved or getattr(recovered[0], 'truncated', False):
        return
    def equivalent(left, right):
        if left[0] != right[0] or left[3] != right[3]:
            return False
        if left[6] != right[6]:
            left = (*left[:6], False, *left[7:])
            right = (*right[:6], False, *right[7:])
        return experience_header(left) == experience_header(right)
    matched = False
    if len(saved) >= len(backup):
        fingerprints = b''.join(experience_identity(row) for row in saved)
        needle = b''.join(experience_identity(row) for row in backup)
        offset = fingerprints.find(needle)
        while offset >= 0:
            if offset % 16 == 0:
                start = offset // 16
                if all(equivalent(a, b) for a, b in zip(saved[start:start + len(backup)], backup)):
                    matched = True
                    break
            offset = fingerprints.find(needle, offset + 1)
    if not matched:
        minimum_overlap = min(3, len(saved), len(backup))
        extension = replay_extension(backup, saved)
        matched = extension is not None and len(saved) - len(extension) >= minimum_overlap
    if matched:
        with file_write_lock(path):
            updated = read_replay(folder, 'recovery')
            if updated is not None and updated[1] <= generation and not getattr(updated[0], 'truncated', False) and stored_experience_digest(updated[0]) == experience_digest(backup):
                path.unlink(missing_ok=True)


def save_replay(folder, records, slot, generation):
    path = folder / f'experience.{slot}.gz'
    with file_write_lock(path):
        tmp = unique_temp_path(path)
        digest = hashlib.sha256()
        entries = list(records)
        if len(entries) > REPLAY_FILE_RECORD_LIMIT:
            tmp.unlink(missing_ok=True)
            raise ValueError('经验数据超出单个检查点的记录上限')
        try:
            with open(tmp, 'wb') as raw:
                with gzip.GzipFile(fileobj=raw, mode='wb', compresslevel=1) as f:
                    head = REPLAY_MAGIC + struct.pack('<IQ', len(entries), generation)
                    f.write(head)
                    digest.update(head)
                    previous_next = None
                    for row in entries:
                        ob, nxt = row[0], row[3]
                        record = experience_header(row)
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
    except (gzip.BadGzipFile, EOFError, zlib.error, ValueError, UnicodeError):
        if path.exists():
            quarantine(path)
        return default
    except OSError:
        return default


def save_json(path, obj):
    with file_write_lock(path):
        tmp = unique_temp_path(path)
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
        if not any(item[1] == 'fingerprint' for item in self.db.execute('PRAGMA table_info(experiences)')):
            self.db.execute('ALTER TABLE experiences ADD COLUMN fingerprint BLOB')
        self.db.execute('CREATE UNIQUE INDEX IF NOT EXISTS experiences_fingerprint ON experiences(fingerprint)')
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
        self.failed_writes = 0
        self.spill = deque(maxlen=max(4, 2 * math.isqrt(REPLAY_LIMIT)))
        self.spill_lock = threading.Lock()
        self.spool_folder = self.folder / '.archive_spool'
        self.spool_folder.mkdir(parents=True, exist_ok=True)
        self.spool_files = deque((path, None, 0.) for path in sorted(self.spool_folder.glob('pending.*.record')))
        self.spool_attempts = Counter()
        self.recovered_writes = 0
        self.archive_jobs = 0
        self.write_ms = deque(maxlen=96)
        self.queue_ms = deque(maxlen=96)
        self.pending = queue.Queue(maxsize=max(4, 2 * math.isqrt(REPLAY_LIMIT)))
        self.replacements = queue.Queue()
        self.archive_condition = threading.Condition()
        self.enqueued_sequence = 0
        self.unfinished_sequences = set()
        self.writer = threading.Thread(target=self._archive_job, daemon=True)
        self.writer.start()

    def _archive_done(self, sequence):
        with self.archive_condition:
            self.unfinished_sequences.discard(sequence)
            self.archive_condition.notify_all()

    def _next_overflow(self):
        with self.spill_lock:
            if self.spool_files:
                path, sequence, ready_at = self.spool_files.popleft()
                if time.monotonic() >= ready_at:
                    return None, path, sequence
                self.spool_files.append((path, sequence, ready_at))
            if self.spill:
                return self.spill.popleft(), None, None
        return None, None, None

    def _retry_spool(self, path, sequence):
        self.spool_attempts[path] += 1
        delay = min(60., 2. ** min(6, self.spool_attempts[path]))
        with self.spill_lock:
            self.spool_files.append((path, sequence, time.monotonic() + delay))

    def _archive_job(self):
        while True:
            from_queue = False
            from_replacement = False
            spool_path = None
            sequence = None
            item = None
            if self.archive_jobs % 8 == 0:
                item, spool_path, sequence = self._next_overflow()
            if item is None and spool_path is None:
                try:
                    item = self.replacements.get_nowait()
                    from_replacement = True
                except queue.Empty:
                    try:
                        item = self.pending.get(timeout=.05)
                        from_queue = True
                    except queue.Empty:
                        item, spool_path, sequence = self._next_overflow()
                        if item is None and spool_path is None:
                            continue
            self.archive_jobs += 1
            completed = False
            try:
                if from_queue and item is None:
                    return
                if spool_path is not None:
                    from_replacement = spool_path.name.startswith('pending.replace.')
                    try:
                        row = self.unpack(spool_path.read_bytes())
                    except OSError as error:
                        self.error = type(error).__name__ + ': ' + str(error)[:140]
                        self.failed_writes += 1
                        self._retry_spool(spool_path, sequence)
                        continue
                    except (ValueError, zlib.error, struct.error) as error:
                        self.error = type(error).__name__ + ': ' + str(error)[:140]
                        self.failed_writes += 1
                        self.dropped += 1
                        quarantine(spool_path)
                        self.spool_attempts.pop(spool_path, None)
                        completed = True
                        continue
                    item = (row, time.monotonic(), sequence)
                row, queued, sequence = item
                started = time.monotonic()
                self.queue_ms.append((started - queued) * 1000.)
                try:
                    self._remember(row, replacement=from_replacement)
                    if spool_path is not None:
                        spool_path.unlink(missing_ok=True)
                        self.spool_attempts.pop(spool_path, None)
                        self.recovered_writes += 1
                    completed = True
                    self.error = ''
                except Exception as error:
                    self.error = type(error).__name__ + ': ' + str(error)[:140]
                    self.failed_writes += 1
                    if spool_path is not None:
                        self._retry_spool(spool_path, sequence)
                    else:
                        try:
                            self._spool_to_disk(item, replacement=from_replacement)
                        except (OSError, MemoryError, ValueError, zlib.error) as spill_error:
                            self.error = '归档写入和备用落盘均失败：' + str(spill_error)[:120]
                            self.dropped += 1
                            completed = True
                finally:
                    self.write_ms.append((time.monotonic() - started) * 1000.)
            finally:
                if from_queue:
                    self.pending.task_done()
                if from_replacement and spool_path is None:
                    self.replacements.task_done()
                if completed and sequence is not None:
                    self._archive_done(sequence)

    @staticmethod
    def spill_priority(row):
        reward = abs(float(row[5]))
        efficacy = max(0., min(1., float(row[11])))
        demonstration = bool(len(row) > 13 and row[13])
        verified = bool(len(row) > 14 and row[14] & CAPTURE_VERIFIED)
        return 4. * demonstration + 2. * verified + min(1., reward) + efficacy * .5

    @staticmethod
    def pack(row):
        return zlib.compress(experience_header(row) + row[0] + row[3], level=1)

    @staticmethod
    def unpack(blob):
        inflater = zlib.decompressobj()
        size = REPLAY_PACK.size + VIS_N * 2
        data = inflater.decompress(blob, size + 1)
        if not inflater.eof or inflater.unused_data or len(data) != size:
            raise ValueError('长期经验记录长度错误')
        values = REPLAY_PACK.unpack(data[:REPLAY_PACK.size])
        action, executed, reward, done, dt, efficacy, reserved, capture_code, action_mask, next_mask = values[:10]
        demonstration = bool(executed & DEMONSTRATION_FLAG)
        executed &= ~DEMONSTRATION_FLAG
        if (action >= ACT_N or executed >= ACT_N or not math.isfinite(dt) or dt <= 0. or
                action_mask != encode_action_mask(action_mask) or next_mask != encode_action_mask(next_mask) or
                not 0. <= efficacy <= 1. or not all(math.isfinite(v) for v in values[2:])):
            raise ValueError('长期经验记录无效')
        numeric = values[10:]
        return (data[REPLAY_PACK.size:REPLAY_PACK.size + VIS_N], tuple(numeric[:META_N]), action,
                data[REPLAY_PACK.size + VIS_N:], tuple(numeric[META_N:META_N * 2]),
                float(reward), bool(done), float(dt), tuple(numeric[META_N * 2:META_N * 2 + CTRL_N]),
                tuple(numeric[META_N * 2 + CTRL_N:]), executed, float(efficacy), bool(reserved), demonstration, int(capture_code), int(action_mask), int(next_mask))

    def _spool_to_disk(self, entry, replacement=False):
        row, queued, sequence = entry
        space = shutil.disk_usage(self.spool_folder)
        if space.free <= MIN_ARCHIVE_RESERVE_BYTES:
            raise OSError('数据磁盘剩余空间不足，无法保存归档溢出经验')
        temporary = unique_temp_path(self.spool_folder / 'pending')
        prefix = 'pending.replace.' if replacement else 'pending.'
        destination = self.spool_folder / (prefix + os.urandom(12).hex() + '.record')
        try:
            with temporary.open('wb') as stream:
                stream.write(self.pack(row))
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, destination)
        finally:
            temporary.unlink(missing_ok=True)
        with self.spill_lock:
            self.spool_files.append((destination, sequence, 0.))

    def remember(self, row, replacement=False):
        with self.archive_condition:
            if row[12] or self.closed:
                return
            self.enqueued_sequence += 1
            sequence = self.enqueued_sequence
            self.unfinished_sequences.add(sequence)
        entry = (row, time.monotonic(), sequence)
        if replacement:
            self.replacements.put_nowait(entry)
            return
        try:
            self.pending.put_nowait(entry)
        except queue.Full:
            self.backpressure += 1
            displaced = None
            with self.spill_lock:
                if len(self.spill) < self.spill.maxlen:
                    self.spill.append(entry)
                else:
                    weakest = min(range(len(self.spill)), key=lambda index: self.spill_priority(self.spill[index][0]))
                    if self.spill_priority(row) >= self.spill_priority(self.spill[weakest][0]):
                        displaced = self.spill[weakest]
                        del self.spill[weakest]
                        self.spill.append(entry)
                    else:
                        displaced = entry
            if displaced is not None:
                try:
                    self._spool_to_disk(displaced)
                except (OSError, MemoryError, ValueError, zlib.error) as error:
                    self.error = '归档溢出经验无法落盘：' + str(error)[:120]
                    self.dropped += 1
                    self.failed_writes += 1
                    self._archive_done(displaced[2])

    def _remember(self, row, replacement=False):
        with self.lock:
            if self.db is None:
                raise RuntimeError('长期经验数据库已关闭')
            self.db.execute('BEGIN IMMEDIATE')
            try:
                if replacement:
                    payload = self.pack(row)
                    fingerprint = experience_identity(row)
                    updated = self.db.execute(
                        'UPDATE experiences SET data=?,priority=max(priority,?),added=? WHERE fingerprint=?',
                        (payload, 1. + abs(float(row[5])), time.time(), fingerprint))
                    inserted_count = 0
                    if not updated.rowcount:
                        inserted = self.db.execute(
                            'INSERT OR IGNORE INTO experiences(scene,priority,added,data,fingerprint) VALUES(?,?,?,?,?)',
                            (session_signature(row[0]) + bytes((row[2],)),
                             1. + abs(float(row[5])), time.time(), payload, fingerprint))
                        inserted_count = int(inserted.rowcount > 0)
                    self.db.execute('COMMIT')
                    self.kept += inserted_count
                    self.error = ''
                    return
                self.db.execute("INSERT INTO meta(key,value) VALUES('observed',1) "
                                "ON CONFLICT(key) DO UPDATE SET value=value+1")
                new_total = int(self.db.execute("SELECT value FROM meta WHERE key='observed'").fetchone()[0])
                magnitude = abs(float(row[5]))
                rate = 1. / math.sqrt(new_total)
                delta = magnitude - self.mean
                new_mean = self.mean + rate * delta
                new_variance = self.variance + rate * (delta * delta - self.variance)
                scene = session_signature(row[0]) + bytes((row[2],))
                visits = self.seen.get(scene, 0) + 1
                surprise = magnitude >= new_mean + math.sqrt(max(0., new_variance))
                periodic = new_total - self.last_saved >= max(1, int(math.sqrt(max(1, self.kept))))
                demonstration = len(row) > 13 and row[13]
                should_keep = (demonstration or visits == 1 or surprise or periodic or
                               random.random() < 1. / math.sqrt(1. + visits))
                inserted_count = 0
                if should_keep:
                    priority = (max(0., magnitude) + 1. / math.sqrt(visits) +
                                max(0., float(row[11])) / math.sqrt(1. + visits) + float(demonstration))
                    payload = self.pack(row)
                    fingerprint = experience_identity(row)
                    inserted = self.db.execute(
                        'INSERT OR IGNORE INTO experiences(scene,priority,added,data,fingerprint) VALUES(?,?,?,?,?)',
                        (scene, priority, time.time(), payload, fingerprint))
                    inserted_count = int(inserted.rowcount > 0)
                self.db.execute('COMMIT')
            except BaseException:
                try:
                    self.db.execute('ROLLBACK')
                except sqlite3.Error:
                    pass
                raise
            self.total = new_total
            self.mean = new_mean
            self.variance = new_variance
            self.seen[scene] = visits
            if len(self.seen) > max(REPLAY_LIMIT, int(math.sqrt(max(1, self.total)) * 12)):
                for key in sorted(self.seen, key=self.seen.get)[:len(self.seen) // 3]:
                    self.seen.pop(key, None)
            if inserted_count:
                self.kept += inserted_count
                self.last_saved = self.total
                if self.total - self.last_prune >= max(32, int(math.sqrt(max(1, self.kept)))):
                    self.last_prune = self.total
                    self._prune()
            self.error = ''

    def _prune(self):
        try:
            capacity = shutil.disk_usage(self.folder)
            bytes_used = sum(p.stat().st_size for p in (self.path, Path(str(self.path) + '-wal')) if p.exists())
            reserve = min(4 * 1024 ** 3, max(MIN_ARCHIVE_RESERVE_BYTES, capacity.total // 50))
            allowed = max(16 * 1024 ** 2, max(0, capacity.free + bytes_used - reserve) // 8)
            if bytes_used <= allowed:
                return
            estimated = max(1, bytes_used // max(1, self.kept))
            excessive = max(1, math.ceil((bytes_used - allowed) / estimated))
            reserved = min(self.kept, max(32, math.isqrt(max(1, self.kept))))
            remove = min(max(0, self.kept - reserved), max(excessive, int(math.sqrt(max(1, self.kept)))))
            if remove:
                self.db.execute('DELETE FROM experiences WHERE id IN (SELECT id FROM experiences ORDER BY priority ASC, id ASC LIMIT ?)', (remove,))
                self.kept = int(self.db.execute('SELECT count(*) FROM experiences').fetchone()[0])
                self.db.execute('PRAGMA incremental_vacuum(' + str(min(16384, max(64, int((bytes_used - allowed) / 4096)))) + ')')
            self.db.execute('PRAGMA wal_checkpoint(TRUNCATE)')
        except (sqlite3.Error, OSError) as error:
            self.error = str(error)[:140]

    def sample(self, count):
        with self.lock:
            try:
                self.kept = int(self.db.execute('SELECT count(*) FROM experiences').fetchone()[0])
            except sqlite3.Error:
                return []
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

    def sync(self, timeout=90.):
        deadline = None if timeout is None else time.monotonic() + max(0., float(timeout))
        with self.archive_condition:
            cutoff = self.enqueued_sequence
            while True:
                unfinished = any(sequence <= cutoff for sequence in self.unfinished_sequences)
                with self.spill_lock:
                    outstanding = bool(self.spill or self.spool_files)
                on_disk = any(self.spool_folder.glob('pending.*.record'))
                if not unfinished and not outstanding and not on_disk:
                    break
                remaining = None if deadline is None else deadline - time.monotonic()
                if remaining is not None and remaining <= 0.:
                    raise TimeoutError('长期经验归档超过等待上限，磁盘待处理记录留待重试')
                self.archive_condition.wait(.05 if remaining is None else min(.05, remaining))
        with self.lock:
            if self.db is None:
                return
            try:
                self.db.execute('PRAGMA wal_checkpoint(PASSIVE)')
            except sqlite3.Error as error:
                self.error = str(error)[:140]
                self.failed_writes += 1
                raise RuntimeError('长期经验 WAL 写盘确认失败') from error
        if self.dropped:
            raise RuntimeError(f'长期归档有 {self.dropped} 条经验未能恢复，保留重放检查点：{self.error[:120]}')

    def close(self):
        with self.archive_condition:
            if self.closed:
                return
            self.closed = True
        sync_failure = None
        try:
            self.sync(timeout=90.)
        except (RuntimeError, TimeoutError, sqlite3.Error) as error:
            sync_failure = error
        self.pending.put(None, timeout=12.)
        self.writer.join(timeout=15.)
        if self.writer.is_alive():
            raise TimeoutError('长期记忆写入线程尚未停止，禁止关闭数据库')
        with self.lock:
            if self.db is not None:
                self.db.close()
                self.db = None
        if sync_failure is not None:
            raise RuntimeError('长期记忆关闭前存在未保存经验，保留重放检查点') from sync_failure


class GoalAtlas:
    def __init__(self, folder):
        self.path = Path(folder) / 'goals.gz'
        self.lock = threading.RLock()
        self.states = {}
        self.edges = {}
        self.demonstrated_elements = {}
        self.total = 0
        self.current_goal = None
        self.current_goal_demonstrated = False
        self.description = '发现可控状态'
        data = read_json(self.path, {})
        if isinstance(data, dict) and data.get('version') in (3, 4):
            try:
                self.states = {str(k): [int(v[0]), float(v[1])] for k, v in data.get('states', {}).items() if len(k) == 16 and len(v) == 2}
                self.edges = {str(k): {str(a): {str(dest): [int(v[0]), float(v[1]), float(v[2]), int(v[3]) if len(v) > 3 else 0]
                                        for dest, v in dests.items() if len(dest) == 16 and len(v) in (3, 4)}
                                         for a, dests in actions.items() if str(a).isdigit() and 0 <= int(a) < ACT_N}
                              for k, actions in data.get('edges', {}).items() if len(k) == 16}
                self.total = max(0, int(data.get('total', 0)))
                if isinstance(data.get('demonstrated_elements'), dict):
                    for scene, entries in data['demonstrated_elements'].items():
                        if not isinstance(scene, str) or len(scene) != 38 or not isinstance(entries, list):
                            continue
                        verified = []
                        for record in entries[:1024]:
                            if (isinstance(record, list) and len(record) == 5 and
                                    isinstance(record[0], str) and 0 < len(record[0]) <= 256 and
                                    record[1] in ('button', 'link', 'tab', 'menu')):
                                try:
                                    cx, cy, trials = float(record[2]), float(record[3]), int(record[4])
                                    if math.isfinite(cx) and math.isfinite(cy) and 0. <= cx <= 1. and 0. <= cy <= 1. and 1 <= trials <= 1000000:
                                        verified.append([record[0], record[1], cx, cy, trials])
                                except (TypeError, ValueError, OverflowError):
                                    pass
                        if verified:
                            self.demonstrated_elements[scene] = verified
            except (TypeError, ValueError, KeyError, AttributeError):
                self.states, self.edges, self.total, self.demonstrated_elements = {}, {}, 0, {}

    def remember_element(self, frame, info, position, region):
        if not safe_demonstrated_element(info, position, allow_unknown=True):
            return False
        label, role, bounds = info
        x, y, w, h = region
        if w <= 0 or h <= 0:
            return False
        left, top, right, bottom = bounds
        cx, cy = ((left + right) / 2. - x) / w, ((top + bottom) / 2. - y) / h
        if not (0. <= cx <= 1. and 0. <= cy <= 1.):
            return False
        scene = element_scene_signature(frame).hex()
        name = ' '.join(str(label).casefold().split())[:256]
        with self.lock:
            entries = self.demonstrated_elements.setdefault(scene, [])
            for item in entries:
                if item[0] == name and item[1] == role and abs(cx - item[2]) <= .025 and abs(cy - item[3]) <= .025:
                    item[4] = min(1000000, item[4] + 1)
                    return True
            entries.append([name, role, round(cx, 5), round(cy, 5), 1])
            limit = max(64, min(4096, 8 * math.isqrt(REPLAY_LIMIT)))
            while sum(map(len, self.demonstrated_elements.values())) > limit:
                victim = min(self.demonstrated_elements, key=lambda key: sum(item[4] for item in self.demonstrated_elements[key]))
                self.demonstrated_elements[victim].pop(0)
                if not self.demonstrated_elements[victim]:
                    del self.demonstrated_elements[victim]
            return True

    def authorizes_element(self, scene, info, position, region):
        if not safe_demonstrated_element(info, position, allow_unknown=True):
            return False
        if not isinstance(scene, bytes) or len(scene) != 19:
            return False
        label, role, bounds = info
        x, y, w, h = region
        if w <= 0 or h <= 0:
            return False
        left, top, right, bottom = bounds
        cx, cy = ((left + right) / 2. - x) / w, ((top + bottom) / 2. - y) / h
        name = ' '.join(str(label).casefold().split())[:256]
        key = scene.hex()
        with self.lock:
            return any(item[0] == name and item[1] == role and
                       abs(item[2] - cx) <= .025 and abs(item[3] - cy) <= .025
                       for item in self.demonstrated_elements.get(key, ()))

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
            if self.total % max(32, math.isqrt(self.total)) == 0:
                edge_limit = max(256, min(16384, limit * 3))
                count = sum(len(targets) for actions in self.edges.values() for targets in actions.values())
                if count > edge_limit:
                    weak = sorted(((entry[0], source, action, target)
                                   for source, actions in self.edges.items()
                                   for action, targets in actions.items()
                                   for target, entry in targets.items()))
                    for _, source, action, target in weak[:count - edge_limit]:
                        self.edges[source][action].pop(target, None)
                    for source, actions in tuple(self.edges.items()):
                        for action in tuple(actions):
                            if not actions[action]:
                                del actions[action]
                        if not actions:
                            del self.edges[source]

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
            save_json(self.path, {'version': 4, 'total': self.total, 'states': self.states,
                                  'edges': self.edges, 'demonstrated_elements': self.demonstrated_elements})


class LiteBrain:
    def __init__(self, folder):
        self.folder = folder
        self.archive = LifelongMemory(folder)
        self.table = {}
        self.actor = {}
        self.visits = {}
        self.imitation_votes = {}
        self.steps = 0
        self.discount_rate = 0.
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.replay_runtime_limit = REPLAY_LIMIT
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
        recovered = list(replay_sources(folder))
        for generation, slot, records in recovered:
            data = read_json(folder / f'learning.{slot}.lite.gz', {})
            if not isinstance(data, dict) or data.get('version') not in (14, 15) or data.get('generation') != generation or data.get('replay_count', len(records)) != getattr(records, 'source_count', len(records)):
                continue
            if data.get('replay_digest') is not None and data['replay_digest'] != stored_experience_digest(records).hex():
                continue
            table = {}
            actor = {}
            visits = {}
            imitation_votes = {}
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
            for key, value in (data.get('imitation_votes') or {}).items() if isinstance(data.get('imitation_votes'), dict) else ():
                try:
                    keybytes = bytes.fromhex(key)
                    numbers = [float(v) for v in value]
                    if len(keybytes) in (CELLS_PER_VIEW * 2 + 5, 14, 13) and len(numbers) == ACT_N and all(math.isfinite(v) and 0. <= v <= 1e9 for v in numbers):
                        imitation_votes[keybytes] = numbers
                except (TypeError, ValueError, OverflowError):
                    continue
            try:
                steps = max(0, int(data.get('steps', 0)))
            except (TypeError, ValueError, OverflowError):
                continue
            self.table, self.actor, self.visits, self.imitation_votes = table, actor, visits, imitation_votes
            self.steps = steps
            self.memory, self.generation, self.slot = records, generation, slot if isinstance(slot, int) else -1
            break
        if recovered:
            generation, slot, records = recovered[0]
            self.latest_replay_generation = generation
            if generation != self.generation:
                additional = replay_extension(self.memory, records) if self.generation and (self.table or self.imitation_votes) else None
                self.memory = records
                self.slot = slot if isinstance(slot, int) else -1
                if additional is None:
                    self.rebuild_from_memory()
                else:
                    self.discount_rate = observed_discount_rate(self.memory)
                    for row in additional:
                        if not row[12]:
                            self.update(row)
            self.steps = max(self.steps, len(records), getattr(records, 'source_count', len(records)))
        elif not self.table:
            self.steps = 0
        if self.memory and not (self.table or self.imitation_votes):
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
            self.imitation_votes.clear()
            for row in self.memory:
                if not row[12]:
                    self.update(row)

    def restore_experience(self, records, steps):
        with self.save_lock:
            self.memory = deque(list(records)[-self.replay_runtime_limit:], maxlen=REPLAY_LIMIT)
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
        groups = ((0, 1, 2, 3), (4, 5, 6, 7, 8), (9, 10, 11, 12, 13, 17), (14, 15, 16, 18, 19, 20, 21, 22, 23))
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

    def scores(self, ob, meta, keys=None):
        keys = self.keys(ob, meta) if keys is None else keys
        q = self.values(ob, meta, keys)
        votes = [self.imitation_votes[key] for key in keys if key in self.imitation_votes]
        if not votes:
            return q
        counts = [sum(part[action] for part in votes) / len(votes) for action in range(ACT_N)]
        baseline = sum(counts) / ACT_N
        spread = math.sqrt(sum((item - baseline) ** 2 for item in counts) / ACT_N)
        if spread <= sys.float_info.epsilon:
            return q
        q = q if q is not None else [0.] * ACT_N
        mean_q = sum(q) / ACT_N
        value_scale = max(.05, math.sqrt(sum((item - mean_q) ** 2 for item in q) / ACT_N))
        evidence = sum(counts)
        confidence = evidence / (evidence + max(4., math.sqrt(1. + self.steps)))
        return [q[action] + .75 * confidence * value_scale * (counts[action] - baseline) / spread for action in range(ACT_N)]

    def choose(self, ob, meta, held, targets=None, allowed_actions=None):
        opts = [action for action in candidates(held) if allowed_actions is None or action in allowed_actions]
        if not opts:
            return IDLE_ACTION, anchor_control(IDLE_ACTION)
        with self.save_lock:
            keys = self.keys(ob, meta)
            q = self.scores(ob, meta, keys)
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
        demonstration = len(row) > 13 and row[13]
        if not demonstration:
            before = self.values(ob, meta, keys)
            after = self.values(nxt, nmeta)
            successors = future_action_candidates(nmeta, row[16] if len(row) > 16 else SAFE_FUTURE_MASK)
            future = max(after[i] for i in successors) if after else 0.
            target = reward + (0. if done else temporal_discount(dt, self.discount_rate) * future)
            baseline = before[action] if before is not None else 0.
            correction = (target - baseline) / math.sqrt(1. + self.visits.get(keys[0], 0))
        for key in keys:
            if demonstration:
                votes = self.imitation_votes.setdefault(key, [0.] * ACT_N)
                votes[action] = min(1e9, votes[action] + max(.01, min(1., float(row[11]))))
            else:
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
        limit = REPLAY_LIMIT * len(keys)
        if max(len(self.table), len(self.imitation_votes)) > limit:
            known = set(self.table) | set(self.imitation_votes)
            evicted = set(sorted(known, key=lambda key: self.visits.get(key, 0))[:max(1, len(known) // 8)])
            for key in evicted:
                self.table.pop(key, None)
                self.imitation_votes.pop(key, None)
                self.visits.pop(key, None)
            self.actor = {key: value for key, value in self.actor.items() if key[:-1] not in evicted}

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False, capture_code=0, action_mask=None, next_action_mask=None):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
            row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration), int(capture_code) & 0xff, encode_action_mask(action_mask), encode_action_mask(next_action_mask if next_action_mask is not None else SAFE_FUTURE_MASK))
            self.memory.append(row)
            while len(self.memory) > self.replay_runtime_limit:
                self.memory.popleft()
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
            q = self.scores(row[0], row[1]) or [0.] * ACT_N
            choices = future_action_candidates(row[1], row[15] if len(row) > 15 else SAFE_FUTURE_MASK)
            best = max(choices, key=lambda a: q[a])
            good += (best == row[2]) if (row[5] > 0. or (len(row) > 13 and row[13])) else (best != row[2])
        return good / len(useful)

    def validation_targets(self, records):
        labels = []
        for row in records:
            after = self.values(row[3], row[4])
            successors = future_action_candidates(row[4], row[16] if len(row) > 16 else SAFE_FUTURE_MASK)
            future = max(after[a] for a in successors) if after else 0.
            labels.append(row[5] + (0. if row[6] else temporal_discount(row[7], self.discount_rate) * future))
        return labels

    def evaluation_losses(self, records, labels):
        losses = []
        for row, target in zip(records, labels):
            if len(row) > 13 and row[13]:
                scores = self.scores(row[0], row[1]) or [0.] * ACT_N
                choices = future_action_candidates(row[1], row[15] if len(row) > 15 else SAFE_FUTURE_MASK)
                losses.append(max(0., max(scores[i] for i in choices) - scores[row[2]]))
            else:
                values = self.values(row[0], row[1])
                error = abs((values[row[2]] if values is not None else 0.) - target)
                losses.append(.5 * error * error if error < 1. else error - .5)
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
            self.sleep_evaluation = (validation, labels, before, quality, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits), baseline_losses, copy.deepcopy(self.imitation_votes))

    def abort_sleep(self):
        with self.save_lock:
            if self.sleep_evaluation is not None:
                self.table = self.sleep_evaluation[4]
                self.actor = self.sleep_evaluation[5]
                self.visits = self.sleep_evaluation[6]
                self.imitation_votes = self.sleep_evaluation[8]
            self.train_memory = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None

    def sleep_progress(self):
        with self.save_lock:
            if self.sleep_evaluation is None:
                return None
            records, labels, before, quality, snapshot, previous_actor, previous_visits, baseline_losses, previous_votes = self.sleep_evaluation
            losses = self.evaluation_losses(records, labels)
            after = sum(losses) / len(losses)
            current = self.policy_metric(records)
            if verified_improvement(records, baseline_losses, losses) and not policy_regressed(quality, current, records):
                if self.sleep_best is None or after < self.sleep_best[0]:
                    self.sleep_best = (after, current, copy.deepcopy(self.table), copy.deepcopy(self.actor), copy.deepcopy(self.visits), copy.deepcopy(self.imitation_votes))
            return {'loss': after, 'verified': self.sleep_best is not None, 'best': self.sleep_best[0] if self.sleep_best is not None else None, 'baseline': before}

    def end_sleep(self):
        with self.save_lock:
            self.train_memory = None
            if self.sleep_evaluation is None:
                return None
            evaluation = self.sleep_progress()
            after = evaluation['loss'] if evaluation is not None else float('nan')
            records, labels, before, quality, snapshot, previous_actor, previous_visits, baseline_losses, previous_votes = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            audit = self.sleep_audit
            self.sleep_audit = None
            current = self.policy_metric(records)
            if best is not None:
                self.table, self.actor, self.visits, self.imitation_votes = best[2:6]
                if audit is not None:
                    audit_rows, audit_targets, audit_before, audit_policy = audit
                    audit_after = self.evaluate(audit_rows, audit_targets)
                    audit_current = self.policy_metric(audit_rows)
                    if not math.isfinite(audit_after) or audit_after > audit_before or policy_regressed(audit_policy, audit_current, audit_rows):
                        self.table, self.actor, self.visits, self.imitation_votes = snapshot, previous_actor, previous_visits, previous_votes
                        return False, before, audit_after, quality, audit_current
                return True, before, best[0], quality, best[1]
            self.table, self.actor, self.visits, self.imitation_votes = snapshot, previous_actor, previous_visits, previous_votes
            degraded = not math.isfinite(after) or after > before or policy_regressed(quality, current, records)
            return (False if degraded else None), before, after, quality, current

    def save(self):
        self.folder.mkdir(parents=True, exist_ok=True)
        with self.checkpoint_lock:
            with self.save_lock:
                memory = list(self.memory)
                generation = max(self.generation, self.latest_replay_generation) + 1
                slot = (self.slot + 1) % 2
                data = {'version': 15, 'generation': generation, 'steps': self.steps, 'replay_count': len(memory), 'replay_digest': experience_digest(memory).hex(), 'table': {k.hex(): v[:] for k, v in self.table.items()}, 'actor': {k.hex(): v[:] for k, v in self.actor.items()}, 'visits': {k.hex(): v for k, v in self.visits.items()}, 'imitation_votes': {k.hex(): v[:] for k, v in self.imitation_votes.items()}}
            save_replay(self.folder, memory, slot, generation)
            save_json(self.folder / f'learning.{slot}.lite.gz', data)
            with self.save_lock:
                self.generation, self.latest_replay_generation, self.slot = generation, generation, slot
            self.archive.sync()
            discard_recovery(self.folder, generation, memory)

    def mark_last_done(self):
        updated = None
        with self.save_lock:
            if self.memory and not self.memory[-1][6]:
                row = self.memory[-1]
                updated = (*row[:6], True, *row[7:])
                self.memory[-1] = updated
        if updated is not None:
            self.archive.remember(updated, replacement=True)

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
        self.sampler_source = None
        self.sampler_built_at = -1
        self.t = torch
        self.d = device
        self.label = label
        self.model_restore_errors = []
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.replay_runtime_limit = REPLAY_LIMIT
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
                self.behavior = nn.Sequential(nn.Linear(160 + META_N, 128), nn.GELU(), nn.Linear(128, ACT_N))
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

            def imitation_logits(self, embedding):
                return self.behavior(embedding)

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
            torch.backends.cudnn.benchmark = False
            try:
                if hasattr(torch.backends.cuda.matmul, 'fp32_precision'):
                    torch.backends.cuda.matmul.fp32_precision = 'tf32'
                    conv_backend = getattr(torch.backends.cudnn, 'conv', None)
                    if hasattr(conv_backend, 'fp32_precision'):
                        conv_backend.fp32_precision = 'tf32'
                else:
                    torch.set_float32_matmul_precision('high')
            except (AttributeError, RuntimeError, ValueError):
                try:
                    torch.set_float32_matmul_precision('high')
                except (AttributeError, RuntimeError, ValueError):
                    pass
        self.use_bfloat16 = False
        self.use_float16 = False
        self.grad_scaler = None
        self.perf = {'transfer_ms': 0., 'inference_ms': 0., 'batches': 0, 'training_examples': 0, 'visual_error': 0.}
        self.inference_durations = deque(maxlen=max(16, math.isqrt(REPLAY_LIMIT)))
        self.cuda_optimizer_steps = 0
        self.cuda_training_path_verified = False
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
        theoretical_capacity = max(1, free_bytes // max(1, tensor_bytes_per_sample * 6)) if free_bytes else REPLAY_LIMIT
        self.batch_limits = {False: min(REPLAY_LIMIT, theoretical_capacity), True: min(REPLAY_LIMIT, theoretical_capacity)}
        initial_batch = max(1, min(self.batch_limits[False], math.isqrt(REPLAY_LIMIT), 8 if getattr(device, 'type', None) == 'cuda' else math.isqrt(REPLAY_LIMIT)))
        self.batch_sizes = {False: initial_batch, True: initial_batch}
        self.training_throughput = {False: 0., True: 0.}
        self.training_latency = {False: 0., True: 0.}
        self.interactive_budget = None
        self.gpu_train_started = 0.
        self.gpu_train_examples = 0
        self.gpu_train_batches = 0
        self.steps = 0
        self.grads = 0
        self.imitation_updates = 0
        self.train_memory = None
        self.sleep_evaluation = None
        self.sleep_best = None
        self.sleep_audit = None
        self.planning_trust = 0.
        self.planning_ratio = None
        self.sleep_initial_capacity = None
        self.sleep_growth_cost = 0.
        replay_pairs = list(replay_sources(folder))
        if replay_pairs:
            self.generation, recovered_slot, self.memory = max(replay_pairs, key=lambda entry: (entry[0], entry[1] == 'recovery'))
            self.slot = recovered_slot if isinstance(recovered_slot, int) else -1
        replay_generations = {slot: generation for generation, slot, _ in replay_pairs if isinstance(slot, int)}
        replay_counts = {slot: getattr(records, 'source_count', len(records)) for generation, slot, records in replay_pairs if isinstance(slot, int)}
        replay_records = {slot: records for generation, slot, records in replay_pairs if isinstance(slot, int)}
        for slot in sorted(replay_generations, key=lambda index: replay_generations[index]):
            path = folder / f'model.{slot}.pt'
            if not path.exists():
                continue
            try:
                state = torch.load(path, map_location='cpu', weights_only=True)
                if state.get('version') not in (19, 20):
                    continue
                legacy_state = state['version'] == 19
                depth = int(state.get('capacity_depth', 0))
                worlds = int(state.get('capacity_world_models', 0))
                visual_depth = int(state.get('capacity_visual_depth', 0))
                if depth < 0 or worlds < 0 or visual_depth < 0 or depth != sum(key.startswith('growing.') and key.endswith('.transform.3.weight') for key in state.get('q', {})) or worlds != sum(key.startswith('world_models.') and key.endswith('.2.weight') for key in state.get('q', {})) or visual_depth != sum(key.startswith('visual_growing.') and key.endswith('.transform.3.weight') for key in state.get('q', {})):
                    continue
                generation = int(state['generation'])
                if generation <= self.model_generation or generation != replay_generations[slot] or state.get('replay_count', replay_counts[slot]) != replay_counts[slot]:
                    continue
                if state.get('replay_digest') is not None and state['replay_digest'] != stored_experience_digest(replay_records[slot]).hex():
                    raise ValueError('模型检查点关联的经验校验不匹配')
                old_depth = len(self.q.growing)
                old_worlds = len(self.q.world_models)
                old_visual_depth = len(self.q.visual_growing)
                before_q = cpu_snapshot(self.t, self.q.state_dict())
                before_target = cpu_snapshot(self.t, self.target.state_dict())
                before_opt = cpu_snapshot(self.t, self.optq.state_dict())
                try:
                    self.resize_capacity(depth, worlds, visual_depth)
                    if legacy_state:
                        for module, weights in ((self.q, state['q']), (self.target, state['target'])):
                            missing, unexpected = module.load_state_dict(weights, strict=False)
                            expected = {key for key in module.state_dict() if key.startswith('behavior.')}
                            if set(missing) != expected or unexpected:
                                raise ValueError('旧模型参数结构不兼容')
                        self.optq.state.clear()
                    else:
                        self.q.load_state_dict(state['q'], strict=True)
                        self.target.load_state_dict(state['target'], strict=True)
                        self.optq.load_state_dict(state['opt'])
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
                self.imitation_updates = max(0, int(state.get('imitation_updates', 0))) if not legacy_state else 0
                self.model_generation = generation
                self.model_slot = slot
            except Exception as error:
                self.model_restore_errors.append(path.name + '：' + type(error).__name__ + '：' + str(error)[:120])
                continue
        if self.model_restore_errors:
            self.label += ' · 检查点恢复警告'
            try:
                save_json(self.folder / '.model_restore_errors.gz', {'when': time.time(), 'errors': self.model_restore_errors[-8:]})
            except (OSError, TypeError, ValueError):
                pass
        self.steps = max(self.steps, len(self.memory))
        self.discount_rate = observed_discount_rate(self.memory)
        self.control_evidence = ControlEvidence(self.memory)
        self.recovery_required = bool(self.memory and (self.generation != self.model_generation or self.slot == -1))
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

    def verify_training_path(self, force=False):
        if getattr(self.d, 'type', None) != 'cuda' and not force:
            return False
        if self.grads and not force:
            return False
        with self.model_lock:
            saved_q = cpu_snapshot(self.t, self.q.state_dict())
            saved_target = cpu_snapshot(self.t, self.target.state_dict())
            saved_opt = cpu_snapshot(self.t, self.optq.state_dict())
            scaler_state = copy.deepcopy(self.grad_scaler.state_dict()) if self.grad_scaler is not None else None
            old_values = (self.grads, self.cuda_optimizer_steps, self.train_memory,
                          self.sampler, self.sampler_key, self.sampler_source, self.sampler_built_at, self.historical_refreshed,
                          self.historical_samples, self.discount_rate, self.gpu_train_started, self.gpu_train_examples,
                          self.gpu_train_batches, self.perf.copy(), self.batch_sizes.copy(),
                          self.batch_limits.copy(), self.training_latency.copy(),
                          self.training_throughput.copy(), self.imitation_updates)
            image_a = bytes(VIS_N)
            image_b = bytes([7]) * VIS_N
            meta = tuple(0. for _ in range(META_N))
            action_a, action_b = IDLE_ACTION, MOTION_ACTIONS[0]
            control_a, control_b = anchor_control(action_a), anchor_control(action_b)
            synthetic = [(image_a, meta, action_a, image_b, meta, .1, True, .05,
                          control_a, control_a, action_a, 1., False, False, CAPTURE_VERIFIED),
                         (image_b, meta, action_b, image_a, meta, .2, True, .05,
                          control_b, control_b, action_b, 1., False, True, CAPTURE_VERIFIED)]
            try:
                self.train_memory = synthetic
                self.sampler_key = None
                self.sampler_source = None
                before = self.grads
                if self.train(1, AnyStop()) < 1 or self.grads <= before:
                    raise RuntimeError('实际训练路径未执行有效优化器更新')
                if getattr(self.d, 'type', None) == 'cuda' and self.cuda_optimizer_steps <= old_values[1]:
                    raise RuntimeError('CUDA 优化器未实际更新参数')
                self.cuda_training_path_verified = True
                return True
            finally:
                self.optq.zero_grad(set_to_none=True)
                self.q.load_state_dict(saved_q, strict=True)
                self.target.load_state_dict(saved_target, strict=True)
                self.optq.load_state_dict(saved_opt)
                if self.grad_scaler is not None and scaler_state is not None:
                    self.grad_scaler.load_state_dict(scaler_state)
                (self.grads, self.cuda_optimizer_steps, self.train_memory,
                 self.sampler, self.sampler_key, self.sampler_source, self.sampler_built_at, self.historical_refreshed,
                 self.historical_samples, self.discount_rate, self.gpu_train_started, self.gpu_train_examples,
                 self.gpu_train_batches, self.perf, self.batch_sizes,
                 self.batch_limits, self.training_latency, self.training_throughput, self.imitation_updates) = old_values
                self.q.eval()
                self.target.eval()

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
        model_evidence = max(layer_evidence, world_model_evidence_floor(parameters, worlds))
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
            self.memory = deque(list(records)[-self.replay_runtime_limit:], maxlen=REPLAY_LIMIT)
            self.control_evidence = ControlEvidence(self.memory)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.sampler_key = None
            self.sampler_source = None
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
                        embedded = self.q(frames, features)[2]
                        predicted = self.q.imitation_logits(embedded)
                        loss = -(weights * t.log_softmax(predicted, dim=-1)).sum(dim=-1).mean()
                    if not bool(t.isfinite(loss).item()):
                        raise ValueError('策略迁移出现非有限训练误差')
                    self.optq.zero_grad(set_to_none=True)
                    if self.grad_scaler is not None:
                        previous_scale = self.grad_scaler.get_scale()
                        self.grad_scaler.scale(loss).backward()
                        self.grad_scaler.unscale_(self.optq)
                        t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.)
                        self.grad_scaler.step(self.optq)
                        self.grad_scaler.update()
                        optimizer_updated = self.grad_scaler.get_scale() >= previous_scale
                    else:
                        loss.backward()
                        t.nn.utils.clip_grad_norm_(self.q.parameters(), 1.)
                        self.optq.step()
                        optimizer_updated = True
                    if optimizer_updated:
                        self.grads += 1
                        if getattr(self.d, 'type', None) == 'cuda':
                            self.cuda_optimizer_steps += 1
                        trained += len(rows)
                        self.imitation_updates += len(rows)
                if trained:
                    self.target.load_state_dict(self.q.state_dict())
                    self.target.eval()
            finally:
                self.q.eval()
        return trained

    def append_experience(self, records, steps):
        with self.save_lock:
            self.memory.extend(records)
            while len(self.memory) > self.replay_runtime_limit:
                self.memory.popleft()
            self.control_evidence = ControlEvidence(self.memory)
            self.steps = max(self.steps, int(steps), len(self.memory))
            self.sampler_key = None
            self.sampler_source = None
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
        packed = bytearray().join(observations)
        source = self.t.frombuffer(packed, dtype=self.t.uint8).reshape(len(observations), CHANNELS * 2, VIS_H, VIS_W)
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

    def policy_scores(self, qvalues, embedding):
        if self.imitation_updates <= 0:
            return qvalues
        logits = self.q.imitation_logits(embedding)
        centered = logits - logits.mean(dim=-1, keepdim=True)
        expert_scale = centered.std(dim=-1, unbiased=False, keepdim=True).clamp(min=1e-4)
        value_scale = qvalues.detach().std(dim=-1, unbiased=False, keepdim=True).clamp(min=.05)
        strength = self.imitation_updates / (self.imitation_updates + max(8., math.sqrt(max(1, len(self.memory)))))
        return qvalues + .75 * strength * value_scale * centered / expert_scale

    def choose(self, ob, meta, held, targets=None, allowed_actions=None):
        allowed = [action for action in candidates(held) if allowed_actions is None or action in allowed_actions]
        if not allowed:
            return IDLE_ACTION, anchor_control(IDLE_ACTION)
        epsilon = adaptive_exploration(self.steps, self.grads)
        if random.random() < epsilon:
            action = explore_action(allowed, meta, self.steps, ob, targets)
            return action, self.control_evidence.explore(action, meta)
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
                    current_likelihood = likelihood.clone()
                    confidence = 1. - adaptive_exploration(self.steps, self.grads)
                    confidence *= self.grads / (self.grads + math.sqrt(max(1, len(self.memory))))
                    metric = self.policy_scores(q, embedding)[0] + confidence * (returns * likelihood - returns.detach().mean())
                    if self.grads > 0:
                        imagined, disagreement = self.q.predict_with_uncertainty(expanded, candidate)
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
                            future_values = self.q.policy(imagined)
                            future_action = future_values.argmax(dim=1)
                            utility = future_values.gather(1, future_action[:, None]).squeeze(1)
                            advantage = (utility - utility.mean()).clamp(-scale, scale)
                            metric = metric + discount * planning_reliability * likelihood * advantage
                            discount *= self.planning_trust * temporal_discount(max(self.perf['inference_ms'] / 1000., sys.float_info.epsilon), self.discount_rate)
                            if discount < 1. / max(1., self.steps + self.grads):
                                break
                            control_options = self.q.policy_controls(imagined)
                            imagined_control = control_options.gather(1, future_action[:, None, None].expand(-1, 1, CTRL_N)).squeeze(1)
                            likelihood = likelihood * self.q.execute_value(imagined, imagined_control)
                            imagined, disagreement = self.q.predict_with_uncertainty(imagined, imagined_control)
                            planning_reliability = planning_reliability / (1. + disagreement.sqrt())
                payload = self.t.cat((metric.float(), output[0].float().reshape(-1), current_likelihood.float())).cpu().tolist()
                values = payload[:ACT_N]
                action = careful_choice(values, allowed, self.grads)
                offset = ACT_N + action * CTRL_N
                control = payload[offset:offset + CTRL_N]
                predicted_efficacy = payload[ACT_N * (CTRL_N + 1) + action]
                trust = confidence * predicted_efficacy / max(1e-7, predicted_efficacy + (1. - predicted_efficacy) * epsilon)
        elapsed = (time.monotonic() - inference_started) * 1000.
        self.perf['inference_ms'] += (elapsed - self.perf['inference_ms']) / math.sqrt(1. + self.steps)
        self.inference_durations.append(elapsed)
        return action, anchor_control(action, control, trust)

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False, capture_code=0, action_mask=None, next_action_mask=None):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
            row = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration), int(capture_code) & 0xff, encode_action_mask(action_mask), encode_action_mask(next_action_mask if next_action_mask is not None else SAFE_FUTURE_MASK))
            self.memory.append(row)
            while len(self.memory) > self.replay_runtime_limit:
                self.memory.popleft()
            self.control_evidence.observe(row)
            self.steps += 1
            if not reserved and (self.steps <= 8 or self.steps % max(4, min(32, math.isqrt(len(self.memory)))) == 0):
                self.discount_rate = observed_discount_rate(self.memory)
        self.archive.remember(row)

    def train(self, count, stop):
        with self.save_lock:
            active = self.train_memory if self.train_memory is not None else self.memory
            sleeping = self.train_memory is not None
            steps = self.steps
            available = len(active)
            refresh = max(2, min(32, math.isqrt(max(1, available))))
            sampler_key = (sleeping, id(self.train_memory) if sleeping else 0)
            rebuild = (self.sampler is None or self.sampler_key != sampler_key or
                       self.sampler_source is None or steps < self.sampler_built_at or
                       steps - self.sampler_built_at >= refresh)
            if rebuild:
                source = list(active)
                indices = [i for i, row in enumerate(source) if not row[12]]
                if len(indices) < 2:
                    return 0
                if not sleeping and len(indices) > max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1)))):
                    width = max(8, int(math.sqrt(len(indices)) * math.sqrt(max(1, os.cpu_count() or 1))))
                    old = indices[:-width]
                    indices = random.sample(old, min(len(old), max(1, width // 2))) + indices[-width:]
                self.sampler = ReplaySampler(source, indices)
                self.sampler_source = source
                self.sampler_key = sampler_key
                self.sampler_built_at = steps
                self.discount_rate = observed_discount_rate(source)
            else:
                source = self.sampler_source
                indices = self.sampler.indices
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
                        if 'out of memory' not in detail:
                            raise
                        mode = self.train_memory is not None
                        old_batch = self.batch_sizes[mode]
                        self.batch_limits[mode] = min(self.batch_limits[mode], max(1, old_batch // 2))
                        self.batch_sizes[mode] = self.batch_limits[mode]
                        traceback.clear_frames(error.__traceback__)
                        error.__traceback__ = None
                        self.optq.zero_grad(set_to_none=True)
                        self.gpu_train_batches = 0
                        self.gpu_train_examples = 0
                        if getattr(self.d, 'type', None) == 'cuda':
                            gc.collect()
                            self.t.cuda.empty_cache()
                        if old_batch <= 1:
                            raise RuntimeError('CUDA out of memory: 单样本训练显存不足，需自动切换其他可用计算设备') from None
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
            if not sleeping and self.interactive_budget is not None:
                throughput = self.training_throughput[False]
                if throughput > 0.:
                    requested_batch = min(requested_batch, max(1, int(throughput * self.interactive_budget)))
                else:
                    requested_batch = 1
                requested_batch = min(4, requested_batch)
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
            verified_demo = t.tensor([len(row) > 14 and row[13] and bool(row[14] & CAPTURE_VERIFIED) for row in immediate], dtype=t.float32, device=self.d)
            autonomous = 1. - demonstration
            autonomous_count = autonomous.sum().clamp(min=1.)
            capture_quality = t.tensor(
                [1. if len(row) > 14 and row[14] & CAPTURE_VERIFIED else
                 .85 if len(row) > 14 and (row[14] & 0x7f) == CAPTURE_SOURCES['gdi'] else .7
                 for row in immediate], dtype=t.float32, device=self.d)
            world_usable = (autonomous + verified_demo) * capture_quality
            world_count = world_usable.sum().clamp(min=1.)
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
                allowed_next = t.tensor(
                    [[action in future_action_candidates(row[4], row[16] if len(row) > 16 else SAFE_FUTURE_MASK)
                      for action in range(ACT_N)] for row in batch],
                    dtype=t.bool, device=self.d)
                online = online.masked_fill(~allowed_next, -1e8)
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
                weighted = bootstrap * world_usable.unsqueeze(0)
                dynamics_loss = (per_head * weighted).sum() / weighted.sum().clamp(min=1.)
            else:
                dynamics_loss = (per_head.mean(dim=0) * world_usable).sum() / world_count
            evidence = (state - immediate_future).abs().mean(dim=(1, 2, 3)).detach() * efficacy * world_usable
            inverse_errors = t.nn.functional.cross_entropy(self.q.infer_action(embedding, future_features.detach()), acts, reduction='none')
            inverse_loss = (inverse_errors * evidence).sum() / evidence.sum().clamp(min=1e-6)
            if len(batch) > 1:
                projection = t.nn.functional.normalize(predicted_future, dim=-1)
                teachers = t.nn.functional.normalize(future_features.detach(), dim=-1)
                logits = (projection @ teachers.T) * math.sqrt(projection.shape[-1])
                signatures = [session_signature(row[3]) for row in immediate]
                duplicate = t.tensor([[i != j and signatures[i] == signatures[j] for j in range(len(signatures))] for i in range(len(signatures))], dtype=t.bool, device=self.d)
                contrastive_errors = t.nn.functional.cross_entropy(logits.masked_fill(duplicate, -1e4), t.arange(len(batch), device=self.d), reduction='none')
                contrastive_loss = (contrastive_errors * world_usable).sum() / world_count
            else:
                contrastive_loss = dynamics_loss * 0.
            advantage = (immediate_reward - effectiveness.detach()).clamp(-1., 1.)
            good = t.sigmoid(advantage / immediate_reward.detach().std(unbiased=False).clamp(min=1e-4))
            desired = ctrl * efficacy[:, None] + intended * (1. - efficacy[:, None])
            auxiliary = ((predicted - desired).square().mean(dim=1) * (good * efficacy * autonomous + demonstration)).mean()
            imitation_loss = (t.nn.functional.cross_entropy(self.q.imitation_logits(embedding), acts, reduction='none') * demonstration).sum() / demonstration.sum().clamp(min=1.)
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
            loss = temporal + effect_loss + execution_loss + auxiliary + imitation_loss + visual_weight * visual_loss + dynamics_weight * (dynamics_loss + inverse_loss + contrastive_loss) - confidence * actor_gain * autonomous.mean()
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
                self.imitation_updates += int(demonstration.sum().item())
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
                imitation_loss = t.nn.functional.cross_entropy(self.q.imitation_logits(features), actions, reduction='none') * demonstration
                segment_loss = (q_loss + effect_loss + execution_loss + dynamics_loss + inverse_loss) * (1. - demonstration) + actor_loss + visual_loss + imitation_loss
                losses.extend(segment_loss.cpu().tolist())
        return losses

    def evaluate(self, entries, labels):
        return sum(self.evaluation_losses(entries, labels)) / max(1, len(entries))

    def performance(self):
        with self.save_lock:
            training = self.training_throughput[self.train_memory is not None]
            metrics = {'world_models': 2 + len(self.q.world_models), 'transfer_ms': round(self.perf['transfer_ms'], 3), 'inference_ms': round(self.perf['inference_ms'], 3), 'training_samples_per_second': round(training, 2), 'batches': self.perf['batches'], 'training_examples': self.perf['training_examples'], 'imitation_updates': self.imitation_updates, 'visual_error': round(self.perf['visual_error'], 5), 'batch_size': self.batch_sizes[self.train_memory is not None], 'archive_count': self.archive.kept, 'archive_total_observed': self.archive.total, 'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'model_parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'planning_trust': round(self.planning_trust, 3), 'world_model_ratio': round(self.planning_ratio, 3) if self.planning_ratio is not None else None}
            if self.inference_durations:
                timings = sorted(self.inference_durations)
                metrics['inference_p95_ms'] = round(timings[int(.95 * (len(timings) - 1))], 3)
            if getattr(self.d, 'type', None) == 'cuda':
                metrics['cuda_model_validated'] = all(p.device == self.d for p in self.q.parameters())
                metrics['cuda_training_path_verified'] = self.cuda_training_path_verified
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
                logits, _, embedding = self.q(self.images([r[0] for r in part]), self.t.tensor([r[1] for r in part], dtype=self.t.float32, device=self.d))
                q = self.policy_scores(logits, embedding).cpu().tolist()
                for row, scores in zip(part, q):
                    choices = future_action_candidates(row[1], row[15] if len(row) > 15 else SAFE_FUTURE_MASK)
                    chosen = max(choices, key=lambda a: scores[a])
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
                allowed_next = t.tensor(
                    [[action in future_action_candidates(row[4], row[16] if len(row) > 16 else SAFE_FUTURE_MASK)
                      for action in range(ACT_N)] for row in segment],
                    dtype=t.bool, device=self.d)
                online = online.masked_fill(~allowed_next, -1e8)
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
            self.sampler_source = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None
            self.sleep_initial_capacity = (len(self.q.growing), self.growth_at_step, self.growth_attempts, len(self.q.world_models), self.world_growth_at_step, len(self.q.visual_growing), self.visual_growth_at_step)
            initial_parameters = sum(p.numel() for p in self.q.parameters())
            split = sleep_split(records)
            if split is None:
                self.train_memory = []
                return
            self.train_memory, validation, audit = split
            self.discount_rate = observed_discount_rate(self.train_memory)
            self.grow_from_evidence(self.train_memory, validation)
            self.sleep_growth_cost = max(0., (sum(p.numel() for p in self.q.parameters()) - initial_parameters) / max(1, initial_parameters))
            labels = self.validation_targets(validation)
            audit_labels = self.validation_targets(audit)
            audit_losses = self.evaluation_losses(audit, audit_labels)
            self.sleep_audit = (audit, audit_labels, sum(audit_losses) / len(audit), self.policy_metric(audit), self.effect_metric(audit), self.dynamics_metric(audit))
            baseline_losses = self.evaluation_losses(validation, labels)
            before = sum(baseline_losses) / len(validation)
            quality = self.policy_metric(validation)
            effect_before = self.effect_metric(validation)
            dynamics_before = self.dynamics_metric(validation)
            self.sleep_evaluation = (validation, labels, before, quality, cpu_snapshot(self.t, self.q.state_dict()), cpu_snapshot(self.t, self.target.state_dict()), cpu_snapshot(self.t, self.optq.state_dict()), self.grads, effect_before, dynamics_before, baseline_losses, self.imitation_updates)
            return {'capacity_layers': len(self.q.growing), 'vision_layers': len(self.q.visual_growing), 'world_models': 2 + len(self.q.world_models), 'parameters': sum(parameter.numel() for parameter in self.q.parameters()), 'expanded': any(step == self.steps and step > 0 for step in (self.growth_at_step, self.world_growth_at_step, self.visual_growth_at_step))}

    def abort_sleep(self):
        with self.model_lock:
            if self.sleep_evaluation is not None:
                self.q.load_state_dict(self.sleep_evaluation[4])
                self.target.load_state_dict(self.sleep_evaluation[5])
                self.optq.load_state_dict(self.sleep_evaluation[6])
                self.grads = self.sleep_evaluation[7]
                self.imitation_updates = self.sleep_evaluation[11]
            self.train_memory = None
            self.sampler_key = None
            self.sampler_source = None
            self.sleep_evaluation = None
            self.sleep_best = None
            self.sleep_audit = None
            self.sleep_growth_cost = 0.
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
                    self.sleep_best = (after, current, cpu_snapshot(self.t, self.q.state_dict()), cpu_snapshot(self.t, self.target.state_dict()), cpu_snapshot(self.t, self.optq.state_dict()), self.grads, self.imitation_updates)
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
            self.sampler_source = None
            if self.sleep_evaluation is None:
                self.rollback_sleep_capacity()
                return None
            evaluation = self.sleep_progress()
            after = evaluation['loss'] if evaluation is not None else float('nan')
            records, labels, before, quality, old_q, old_target, old_opt, old_grads, old_effect, old_dynamics, baseline_losses, old_imitation = self.sleep_evaluation
            self.sleep_evaluation = None
            best = self.sleep_best
            self.sleep_best = None
            audit = self.sleep_audit
            self.sleep_audit = None
            current = self.policy_metric(records)
            growth_cost = self.sleep_growth_cost
            self.sleep_growth_cost = 0.
            relative_gain = ((before - best[0]) / max(abs(before), sys.float_info.epsilon)) if best is not None else 0.
            minimum_gain = growth_cost / math.sqrt(max(1, len(records)))
            if best is not None and relative_gain > minimum_gain:
                self.q.load_state_dict(best[2])
                self.target.load_state_dict(best[3])
                self.optq.load_state_dict(best[4])
                self.grads = best[5]
                self.imitation_updates = best[6]
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
                        self.imitation_updates = old_imitation
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
            self.imitation_updates = old_imitation
            self.rollback_sleep_capacity()
            if audit is not None:
                self.calibrate_planning(audit[0])
            degraded = not math.isfinite(after) or after > before or policy_regressed(quality, current, records)
            return (False if degraded else None), before, after, quality, current

    def export_transfer(self, name):
        path = Path(name)
        if path.parent.resolve() != self.folder.resolve():
            raise ValueError('模型迁移文件必须保存在当前数据目录')
        with self.model_lock:
            snapshot = {
                'version': 1,
                'q': cpu_snapshot(self.t, self.q.state_dict()),
                'target': cpu_snapshot(self.t, self.target.state_dict()),
                'opt': cpu_snapshot(self.t, self.optq.state_dict()),
                'steps': self.steps,
                'grads': self.grads,
                'imitation_updates': self.imitation_updates,
                'capacity_depth': len(self.q.growing),
                'capacity_visual_depth': len(self.q.visual_growing),
                'capacity_world_models': len(self.q.world_models),
                'growth_at_step': self.growth_at_step,
                'growth_attempts': self.growth_attempts,
                'world_growth_at_step': self.world_growth_at_step,
                'visual_growth_at_step': self.visual_growth_at_step,
                'planning_trust': self.planning_trust,
                'planning_ratio': self.planning_ratio,
            }
            with open(path, 'wb') as stream:
                self.t.save(snapshot, stream)
                stream.flush()
                os.fsync(stream.fileno())
        return path.stat().st_size

    def import_transfer(self, name):
        path = Path(name)
        if path.parent.resolve() != self.folder.resolve():
            raise ValueError('模型迁移文件必须来自当前数据目录')
        snapshot = self.t.load(path, map_location='cpu', weights_only=True)
        if not isinstance(snapshot, dict) or snapshot.get('version') != 1:
            raise ValueError('模型迁移格式不兼容')
        depth = int(snapshot['capacity_depth'])
        worlds = int(snapshot['capacity_world_models'])
        visual = int(snapshot['capacity_visual_depth'])
        if min(depth, worlds, visual) < 0 or max(depth, worlds, visual) > 128:
            raise ValueError('模型迁移容量非法')
        with self.model_lock:
            original_capacity = (len(self.q.growing), len(self.q.world_models), len(self.q.visual_growing))
            original_q = cpu_snapshot(self.t, self.q.state_dict())
            original_target = cpu_snapshot(self.t, self.target.state_dict())
            original_opt = cpu_snapshot(self.t, self.optq.state_dict())
            original_status = (self.steps, self.grads, self.imitation_updates, self.growth_at_step, self.growth_attempts,
                               self.world_growth_at_step, self.visual_growth_at_step,
                               self.planning_trust, self.planning_ratio)
            try:
                self.resize_capacity(depth, worlds, visual)
                self.q.load_state_dict(snapshot['q'], strict=True)
                self.target.load_state_dict(snapshot['target'], strict=True)
                optimizer_layout = [{key: value for key, value in group.items() if key != 'params'}
                                    for group in self.optq.param_groups]
                optimizer_restored = True
                try:
                    self.optq.load_state_dict(snapshot['opt'])
                    for parameter, state in self.optq.state.items():
                        for key, value in state.items():
                            if self.t.is_tensor(value) and (
                                    not bool(self.t.isfinite(value).all().item()) or
                                    (key in ('exp_avg', 'exp_avg_sq', 'max_exp_avg_sq') and
                                     tuple(value.shape) != tuple(parameter.shape))):
                                raise ValueError('旧优化器状态的数值或尺寸不兼容')
                except (KeyError, ValueError, RuntimeError, TypeError):
                    optimizer_restored = False
                    self.optq.state.clear()
                    for group, layout in zip(self.optq.param_groups, optimizer_layout):
                        for key in tuple(group):
                            if key != 'params':
                                group.pop(key)
                        group.update(layout)
                for module in (self.q, self.target):
                    for parameter in module.parameters():
                        if not bool(self.t.isfinite(parameter).all().item()):
                            raise ValueError('迁移后模型权重出现非法数值')
                self.target.eval()
                self.q.eval()
                validate_network(self.t, self, self.d)
                new_steps = max(self.steps, int(snapshot['steps']))
                new_grads = max(0, int(snapshot['grads']))
                new_growth = max(0, int(snapshot['growth_at_step']))
                new_attempts = max(0, int(snapshot['growth_attempts']))
                new_world_growth = max(0, int(snapshot['world_growth_at_step']))
                new_visual_growth = max(0, int(snapshot['visual_growth_at_step']))
                new_trust = float(snapshot['planning_trust'])
                ratio = snapshot['planning_ratio']
                new_ratio = float(ratio) if ratio is not None else None
                if not math.isfinite(new_trust) or (new_ratio is not None and not math.isfinite(new_ratio)):
                    raise ValueError('迁移后规划参数异常')
                self.steps = new_steps
                self.grads = new_grads
                self.imitation_updates = max(0, int(snapshot.get('imitation_updates', 0)))
                self.growth_at_step = new_growth
                self.growth_attempts = new_attempts
                self.world_growth_at_step = new_world_growth
                self.visual_growth_at_step = new_visual_growth
                self.planning_trust = max(0., min(1., new_trust))
                self.planning_ratio = new_ratio
                return {'parameters': sum(p.numel() for p in self.q.parameters()), 'grads': self.grads,
                        'optimizer_restored': optimizer_restored}
            except Exception:
                try:
                    self.resize_capacity(*original_capacity)
                    self.q.load_state_dict(original_q, strict=True)
                    self.target.load_state_dict(original_target, strict=True)
                    self.optq.load_state_dict(original_opt)
                    (self.steps, self.grads, self.imitation_updates, self.growth_at_step, self.growth_attempts,
                     self.world_growth_at_step, self.visual_growth_at_step,
                     self.planning_trust, self.planning_ratio) = original_status
                    self.q.eval()
                    self.target.eval()
                except Exception as rollback_error:
                    raise RuntimeError('模型迁移失败且原模型无法安全回滚，必须停止此后端') from rollback_error
                raise

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
                    snapshot = {'version': 20, 'generation': generation, 'q': cpu_copy(self.q.state_dict()), 'target': cpu_copy(self.target.state_dict()), 'opt': cpu_copy(self.optq.state_dict()), 'steps': steps, 'grads': self.grads, 'imitation_updates': self.imitation_updates, 'replay_count': len(memory), 'replay_digest': experience_digest(memory).hex(), 'capacity_depth': len(self.q.growing), 'capacity_visual_depth': len(self.q.visual_growing), 'capacity_world_models': len(self.q.world_models), 'growth_at_step': self.growth_at_step, 'growth_attempts': self.growth_attempts, 'world_growth_at_step': self.world_growth_at_step, 'visual_growth_at_step': self.visual_growth_at_step}
            path = self.folder / f'model.{model_slot}.pt'
            tmp = unique_temp_path(path)
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
                self.archive.sync()
                discard_recovery(self.folder, generation, memory)
            finally:
                if tmp.exists():
                    try:
                        tmp.unlink()
                    except OSError:
                        pass


    def mark_last_done(self):
        updated = None
        with self.save_lock:
            if self.memory and not self.memory[-1][6]:
                row = self.memory[-1]
                updated = (*row[:6], True, *row[7:])
                self.memory[-1] = updated
        if updated is not None:
            self.archive.remember(updated, replacement=True)

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
        target_parameter = next((p for p in model.parameters() if p.grad is not None and
                                 bool(torch.count_nonzero(p.grad).item())), None)
        if target_parameter is None:
            raise ValueError('计算设备未产生可供更新的梯度')
        original_parameter = target_parameter.detach().clone()
        try:
            trial = torch.optim.AdamW((target_parameter,), lr=0.001)
            trial.step()
            if getattr(device, 'type', None) == 'cuda':
                torch.cuda.synchronize(device)
            if not bool(torch.isfinite(target_parameter).all().item()):
                raise ValueError('优化器产生非法参数')
            if bool(torch.equal(original_parameter, target_parameter)):
                raise ValueError('优化器未实际更新网络参数')
        finally:
            with torch.no_grad():
                target_parameter.copy_(original_parameter)
            if getattr(device, 'type', None) == 'cuda':
                torch.cuda.synchronize(device)
    finally:
        model.zero_grad(set_to_none=True)
        model.eval()
        del frames, meta, controls

RUNTIME_CACHE_VARIABLES = ('TEMP', 'TMP', 'TMPDIR', 'XDG_CACHE_HOME', 'TORCH_HOME',
                           'CUDA_CACHE_PATH', 'TORCHINDUCTOR_CACHE_DIR', 'TRITON_CACHE_DIR',
                           'PIP_CACHE_DIR', 'NUMBA_CACHE_DIR')


def runtime_environment(folder):
    cache = Path(folder) / '.cache'
    cache.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment.update({key: str(cache) for key in RUNTIME_CACHE_VARIABLES})
    return environment


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
    if operation == 'choose' and len(payload) in (4, 5):
        return (bytes(frames.buf[:VIS_N]), *payload[1:])
    if operation == 'learn' and len(payload) in (12, 13, 14, 15, 16):
        return (bytes(frames.buf[:VIS_N]), *payload[1:3], bytes(frames.buf[VIS_N:2 * VIS_N]), *payload[3:])
    raise ValueError('共享画面指令结构异常')


def torch_engine_main(channel, folder_name, runtime_name, backend, cancel_event, preempt_event, shared_name=None, cache_folder=None):
    shared_frames = None
    try:
        if cache_folder is not None:
            scoped = runtime_environment(cache_folder)
            for key in RUNTIME_CACHE_VARIABLES:
                os.environ[key] = scoped[key]
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
            available_cores = (getattr(os, 'process_cpu_count', None) or os.cpu_count)() or 1
            torch.set_num_threads(max(1, min(8, int(available_cores))))
            devices = [(torch.device('cpu'), 'CPU · PyTorch')]
        engine = None
        diagnostics = []
        for device, title in devices:
            candidate = None
            try:
                candidate = TorchBrain.__new__(TorchBrain)
                TorchBrain.__init__(candidate, Path(folder_name), torch, device, title)
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
                if backend == 'cuda':
                    try:
                        candidate.verify_training_path(force=True)
                    except (RuntimeError, ValueError):
                        if not (candidate.use_bfloat16 or candidate.use_float16):
                            raise
                        candidate.use_bfloat16 = False
                        candidate.use_float16 = False
                        candidate.grad_scaler = None
                        candidate.verify_training_path(force=True)
                engine = candidate
                break
            except Exception as error:
                diagnostics.append(str(title) + '：' + str(error)[:160])
                if candidate is not None:
                    try:
                        archive = getattr(candidate, 'archive', None)
                        if archive is not None:
                            archive.close()
                    except Exception:
                        pass
                    candidate = None
                    gc.collect()
                if getattr(device, 'type', None) == 'cuda':
                    try:
                        torch.cuda.empty_cache()
                    except RuntimeError:
                        pass
        if engine is None:
            raise RuntimeError('；'.join(diagnostics) or '没有通过计算验证的设备')
        ready = {'device': str(engine.d), 'cuda_training_verified': bool(engine.cuda_training_path_verified),
                 'parameters_on_device': all(parameter.device == engine.d for parameter in engine.q.parameters())}
        if backend == 'cuda' and (not ready['cuda_training_verified'] or not ready['parameters_on_device']):
            raise RuntimeError('CUDA 训练验证未通过或模型参数未全部位于指定 GPU')
        channel.send(('ready', (engine.label, engine.steps, engine.generation, len(engine.memory), ready)))
        save_thread = None
        save_error = []
        checkpoint_target = 0
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
                elif operation == 'set_replay_limit':
                    limit = max(1, min(REPLAY_LIMIT, int(payload)))
                    with engine.save_lock:
                        engine.replay_runtime_limit = limit
                        while len(engine.memory) > limit:
                            engine.memory.popleft()
                    result = limit
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
                        checkpoint_target = engine.generation + 1
                        save_thread = threading.Thread(target=run_checkpoint, daemon=False)
                        save_thread.start()
                    result = {'target': checkpoint_target}
                elif operation == 'checkpoint_status':
                    result = {'running': bool(save_thread is not None and save_thread.is_alive()),
                              'generation': engine.generation,
                              'error': save_error[0] if save_error else ''}
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
                    result = (engine.train(payload, AnyStop(cancel_event, preempt_event)), engine.performance())
                elif operation == 'policy_metric':
                    result = engine.policy_metric(payload)
                elif operation == 'append_records':
                    records, steps = payload
                    result = engine.append_experience(records, steps)
                elif operation == 'export_transfer':
                    await_checkpoint()
                    result = engine.export_transfer(payload)
                elif operation == 'import_transfer':
                    await_checkpoint()
                    result = engine.import_transfer(payload)
                elif operation == 'mark_last_done':
                    engine.mark_last_done()
                    result = None
                elif operation == 'close':
                    await_checkpoint()
                    engine.archive.close()
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
    def __init__(self, folder, runtime, backend, cancel=None, cache_folder=None):
        self.folder = folder
        self.runtime = Path(runtime) if runtime is not None else None
        self.cache_folder = Path(cache_folder) if cache_folder is not None else Path(folder).parent.parent
        self.engine_backend = backend
        self.accelerated = backend != 'cpu'
        self.memory = deque(maxlen=REPLAY_LIMIT)
        self.replay_runtime_limit = REPLAY_LIMIT
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
        self.last_online_training = time.monotonic()
        self.sleeping = False
        self.interactive = False
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
        self.process = ctx.Process(target=torch_engine_main, args=(endpoint, str(folder), str(runtime) if runtime is not None else None, backend, self.train_cancel, self.train_preempt, self.shared_frames.name if self.shared_frames is not None else None, str(self.cache_folder)), daemon=True)
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
            self.label, self.steps, self.generation, count, diagnostics = value
            self.model_verified = bool(diagnostics.get('parameters_on_device'))
            self.startup_diagnostics = diagnostics
            if not self.model_verified or (backend == 'cuda' and not diagnostics.get('cuda_training_verified')):
                raise RuntimeError('计算后端尚未通过真实模型和训练验证')
            engine_generation = self.generation
            latest = newest_replay(folder)
            recovered = [latest] if latest is not None else []
            if recovered:
                generation, slot, records = recovered[0]
                self.latest_replay_generation = generation
                self.memory = deque(records, maxlen=REPLAY_LIMIT)
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
                    if operation == 'choose' and len(payload) in (4, 5) and isinstance(payload[0], bytes) and len(payload[0]) == VIS_N:
                        shared.buf[:VIS_N] = payload[0]
                        payload = (SHARED_FRAME_TOKEN, *payload[1:])
                    elif operation == 'learn' and len(payload) in (13, 14, 15, 16, 17) and isinstance(payload[0], bytes) and isinstance(payload[3], bytes) and len(payload[0]) == len(payload[3]) == VIS_N:
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

    def choose(self, ob, meta, held, targets=None, allowed_actions=None):
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
            result = self._request('choose', (ob, meta, held, targets, allowed_actions), timeout=15)
            self.inference_wait.append(time.monotonic() - started)
            return result
        finally:
            elapsed = time.monotonic() - started
            self.recent_inference_cost += (elapsed - self.recent_inference_cost) / math.sqrt(1. + self.steps)
            self.recent_inference = time.monotonic()
            self.inference_pending.clear()
            self.train_preempt.clear()

    def learn(self, ob, meta, action, nxt, nmeta, reward, done, dt, ctrl, intended, executed_action, efficacy, reserved=False, demonstration=False, capture_code=0, action_mask=None, next_action_mask=None):
        with self.save_lock:
            ob = coalesce_observation(self.memory, ob)
        data = (ob, tuple(meta), int(action), nxt, tuple(nmeta), float(reward), bool(done), float(dt), tuple(ctrl), tuple(intended), int(executed_action), float(efficacy), bool(reserved), bool(demonstration), int(capture_code) & 0xff, encode_action_mask(action_mask), encode_action_mask(next_action_mask if next_action_mask is not None else SAFE_FUTURE_MASK))
        self.inference_pending.set()
        self.train_preempt.set()
        try:
            self._request('learn', data, timeout=15)
            with self.save_lock:
                self.memory.append(data)
                while len(self.memory) > self.replay_runtime_limit:
                    self.memory.popleft()
                self.steps += 1
        finally:
            self.inference_pending.clear()
            self.train_preempt.clear()

    def set_replay_limit(self, limit):
        limit = max(1, min(REPLAY_LIMIT, int(limit)))
        with self.save_lock:
            if self.replay_runtime_limit == limit:
                return
        applied = int(self._request('set_replay_limit', limit, timeout=15))
        with self.save_lock:
            self.replay_runtime_limit = applied
            while len(self.memory) > applied:
                self.memory.popleft()

    def train(self, count, stop):
        if stop.is_set() or self.train_cancel.is_set() or self.inference_pending.is_set() or self.train_preempt.is_set():
            return 0
        forced = False
        if not self.sleeping and self.interactive and self.inference_interval > 0.:
            idle = max(0., time.monotonic() - self.recent_inference)
            allowed = self.inference_interval - idle - self.recent_inference_cost
            if allowed <= 0. or (self.online_train_cost and self.online_train_cost >= allowed):
                self.online_train_deferrals += 1
                minimum_gap = max(5., 8. * self.online_train_cost, 12. * self.inference_interval)
                forced = (self.online_train_deferrals >= max(4, min(32, math.isqrt(max(1, len(self.memory)))))
                          and time.monotonic() - self.last_online_training >= minimum_gap)
                if not forced:
                    return 0
        if not self.rpc_lock.acquire(blocking=False):
            return 0
        try:
            if stop.is_set() or self.inference_pending.is_set() or self.train_preempt.is_set():
                return 0
            batches = min(max(1, int(count)), max(1, int(4 * math.sqrt(math.log2(2. + len(self.memory))))) if self.sleeping else 1)
            if not forced and not self.sleeping and self.interactive and self.inference_interval and time.monotonic() - self.recent_inference >= self.inference_interval:
                return 0
            if self.sleeping or not self.interactive:
                budget = None
            else:
                measured = sorted(self.inference_wait)
                typical = measured[len(measured) // 2] if measured else (self.recent_inference_cost or self.inference_interval)
                budget = max(sys.float_info.epsilon, min(.05 if forced else .1, .5 * (self.inference_interval or typical), typical))
            samples_per_second = self.latest_perf.get('training_samples_per_second', 0.)
            estimated = (batches * max(1, self.latest_perf.get('batch_size', 1)) / samples_per_second) if samples_per_second else 0.
            started = time.monotonic()
            result, perf = self._request('train', (batches, budget), timeout=max(45., 4. * estimated + self.recent_inference_cost))
            elapsed = time.monotonic() - started
            if not self.sleeping:
                self.online_train_cost = elapsed if not self.online_train_cost else .8 * self.online_train_cost + .2 * elapsed
                if result:
                    self.last_online_training = time.monotonic()
                    self.online_train_deferrals = 0
            self.latest_perf = perf
            return result
        finally:
            self.rpc_lock.release()

    def cancel_train(self):
        self.train_cancel.set()
        self.train_preempt.set()

    def preempt_training(self):
        self.train_preempt.set()

    def reset_train_cancel(self):
        self.train_cancel.clear()

    def reset_train_preempt(self):
        if not self.inference_pending.is_set():
            self.train_preempt.clear()

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
        entries = list(records)[-min(REPLAY_LIMIT, self.replay_runtime_limit):]
        count = max(int(steps), len(entries))
        self._request('sync', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries[-self.replay_runtime_limit:], maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def sync_fast(self, records, steps):
        entries = list(records)[-min(REPLAY_LIMIT, self.replay_runtime_limit):]
        count = max(int(steps), len(entries))
        self._request('sync_fast', (entries, count), timeout=120)
        with self.save_lock:
            self.memory = deque(entries[-self.replay_runtime_limit:], maxlen=REPLAY_LIMIT)
            self.steps = max(self.steps, count)

    def distill_policy(self, samples, stop):
        if stop.is_set() or not samples:
            return 0
        return self._request('distill_policy', samples, timeout=120)

    def warm_train(self, batches, stop):
        if stop.is_set() or batches <= 0:
            return 0
        trained, perf = self._request('warm_train', batches, timeout=120)
        self.latest_perf = perf
        return trained

    def policy_metric(self, records):
        return self._request('policy_metric', list(records), timeout=45)

    def append_records(self, records, steps):
        entries = list(records)
        if not entries:
            return
        self._request('append_records', (entries, int(steps)), timeout=120)
        with self.save_lock:
            self.memory.extend(entries)
            while len(self.memory) > self.replay_runtime_limit:
                self.memory.popleft()
            self.steps = max(self.steps, int(steps), len(self.memory))

    def transfer_policy_to(self, destination):
        if not isinstance(destination, RemoteBrain) or self.folder != destination.folder:
            raise ValueError('模型迁移要求两个计算引擎使用同一个数据目录')
        path = unique_temp_path(self.folder / 'backend_transfer.pt')
        try:
            self._request('export_transfer', str(path), timeout=120)
            result = destination._request('import_transfer', str(path), timeout=120)
            return result
        finally:
            path.unlink(missing_ok=True)

    def checkpoint(self):
        with self.checkpoint_lock:
            result = self._request('checkpoint_async', timeout=10)
            return int(result['target'])

    def await_checkpoint(self, generation, stop=None, timeout=100.):
        deadline = time.monotonic() + timeout
        while True:
            result = self._request('checkpoint_status', timeout=12)
            if result['error']:
                raise RuntimeError('模型检查点写入失败：' + result['error'])
            if not result['running'] and int(result['generation']) >= generation:
                self.generation = max(self.generation, int(result['generation']))
                self.latest_replay_generation = max(self.latest_replay_generation, self.generation)
                return self.generation
            if time.monotonic() >= deadline:
                raise TimeoutError('模型检查点未在限定时间内完成')
            if stop is not None and stop.wait(.25):
                raise InterruptedError('等待检查点写入已取消，后台写入仍可能继续')
            if stop is None:
                time.sleep(.25)

    def save(self):
        with self.checkpoint_lock:
            generation, slot = self._request('save', (max(self.generation, self.latest_replay_generation), self.slot), timeout=100)
            self.generation, self.latest_replay_generation, self.slot = generation, generation, slot

    def close(self):
        if self.closed:
            return
        self.train_cancel.set()
        self.train_preempt.set()
        with self.rpc_lock:
            if self.closed:
                return
            self.closed = True
            self.sleeping = False
            close_error = None
            try:
                try:
                    alive = self.process.is_alive()
                except (AssertionError, ValueError):
                    alive = False
                if alive and not self.failed:
                    try:
                        self.sequence += 1
                        identifier = self.sequence
                        self.channel.send((identifier, 'close', None))
                        if not self.channel.poll(100.):
                            raise TimeoutError('计算进程关闭期间未能确认长期经验已归档')
                        response = self.channel.recv()
                        if not isinstance(response, tuple) or len(response) != 3 or response[1] != identifier:
                            raise RuntimeError('计算进程关闭回复与请求编号不匹配')
                        if response[0] != 'ok':
                            raise RuntimeError(str(response[2]))
                    except (OSError, EOFError, RuntimeError, TimeoutError, ValueError) as error:
                        close_error = error
                if alive:
                    self.process.join(timeout=5)
                    if self.process.is_alive():
                        self.process.terminate()
                        self.process.join(timeout=3)
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
            if close_error is not None:
                raise RuntimeError('计算进程关闭未能确认全部归档完成：' + str(close_error)[:140]) from close_error


if os.name == 'nt':
    from ctypes import wintypes
    u = ctypes.WinDLL('user32', use_last_error=True)
    g = ctypes.WinDLL('gdi32', use_last_error=True)

    class POINT(ctypes.Structure):
        _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

    class ACCESSIBLE_VALUE(ctypes.Union):
        _fields_ = [('lVal', ctypes.c_int32), ('pdispVal', ctypes.c_void_p), ('bstrVal', ctypes.c_void_p),
                    ('reserved', ctypes.c_byte * 16)]

    class ACCESSIBLE_VARIANT(ctypes.Structure):
        _anonymous_ = ('value',)
        _fields_ = [('vt', ctypes.c_ushort), ('reserved1', ctypes.c_ushort),
                    ('reserved2', ctypes.c_ushort), ('reserved3', ctypes.c_ushort),
                    ('value', ACCESSIBLE_VALUE)]

    oleacc = ctypes.WinDLL('oleacc', use_last_error=True)
    oleaut = ctypes.WinDLL('oleaut32', use_last_error=True)
    ole32 = ctypes.WinDLL('ole32', use_last_error=True)
    oleacc.AccessibleObjectFromPoint.argtypes = (POINT, ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(ACCESSIBLE_VARIANT))
    oleacc.AccessibleObjectFromPoint.restype = ctypes.c_long
    oleaut.SysFreeString.argtypes = (ctypes.c_void_p,)
    oleaut.VariantClear.argtypes = (ctypes.POINTER(ACCESSIBLE_VARIANT),)
    oleaut.VariantClear.restype = ctypes.c_long
    ole32.CoInitializeEx.argtypes = (ctypes.c_void_p, ctypes.c_uint32)
    ole32.CoInitializeEx.restype = ctypes.c_long

    def accessible_element_at(position):
        pointer = ctypes.c_void_p()
        child = ACCESSIBLE_VARIANT()
        if oleacc.AccessibleObjectFromPoint(POINT(int(position[0]), int(position[1])), ctypes.byref(pointer), ctypes.byref(child)) < 0 or not pointer.value:
            return None
        try:
            methods = ctypes.cast(pointer, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
            name_ptr = ctypes.c_void_p()
            name_func = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ACCESSIBLE_VARIANT, ctypes.POINTER(ctypes.c_void_p))(methods[10])
            label = ''
            if name_func(pointer, child, ctypes.byref(name_ptr)) >= 0 and name_ptr.value:
                try:
                    label = ctypes.wstring_at(name_ptr.value)
                finally:
                    oleaut.SysFreeString(name_ptr)
            role_value = ACCESSIBLE_VARIANT()
            role_func = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ACCESSIBLE_VARIANT, ctypes.POINTER(ACCESSIBLE_VARIANT))(methods[13])
            role = int(role_value.lVal) if role_func(pointer, child, ctypes.byref(role_value)) >= 0 and role_value.vt == 3 else 0
            category = {0x2b: 'button', 0x1e: 'link', 0x25: 'tab', 0x0c: 'menu'}.get(role, 'other')
            left, top, width, height = (ctypes.c_long() for _ in range(4))
            location_func = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ctypes.POINTER(ctypes.c_long),
                                              ctypes.POINTER(ctypes.c_long), ctypes.POINTER(ctypes.c_long),
                                              ctypes.POINTER(ctypes.c_long), ACCESSIBLE_VARIANT)(methods[22])
            bounds = None
            if location_func(pointer, ctypes.byref(left), ctypes.byref(top), ctypes.byref(width), ctypes.byref(height), child) >= 0:
                if 0 < width.value < 32768 and 0 < height.value < 32768:
                    bounds = (left.value, top.value, left.value + width.value, top.value + height.value)
            return label[:256], category, bounds
        finally:
            oleaut.VariantClear(ctypes.byref(child))
            methods = ctypes.cast(pointer, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
            ctypes.WINFUNCTYPE(ctypes.c_ulong, ctypes.c_void_p)(methods[2])(pointer)

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
    u.GetWindow.argtypes = (wintypes.HWND, wintypes.UINT)
    u.GetWindow.restype = wintypes.HWND
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
    kernel32.CreateMutexW.argtypes = (ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR)
    kernel32.CreateMutexW.restype = wintypes.HANDLE
    kernel32.WaitForSingleObject.argtypes = (wintypes.HANDLE, wintypes.DWORD)
    kernel32.WaitForSingleObject.restype = wintypes.DWORD
    kernel32.ReleaseMutex.argtypes = (wintypes.HANDLE,)
    kernel32.ReleaseMutex.restype = wintypes.BOOL
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
    u.ReleaseDC.restype = ctypes.c_int
    g.GetDeviceCaps.argtypes = (wintypes.HDC, ctypes.c_int)
    g.GetDeviceCaps.restype = ctypes.c_int
    g.CreateCompatibleDC.argtypes = (wintypes.HDC,)
    g.CreateCompatibleDC.restype = wintypes.HDC
    g.CreateDIBSection.argtypes = (wintypes.HDC, ctypes.POINTER(BITMAPINFO), wintypes.UINT, ctypes.POINTER(ctypes.c_void_p), wintypes.HANDLE, wintypes.DWORD)
    g.CreateDIBSection.restype = wintypes.HBITMAP
    g.SelectObject.argtypes = (wintypes.HDC, wintypes.HGDIOBJ)
    g.SelectObject.restype = wintypes.HGDIOBJ
    g.StretchBlt.argtypes = (wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.DWORD)
    g.StretchBlt.restype = wintypes.BOOL
    g.BitBlt.argtypes = (wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.HDC, ctypes.c_int, ctypes.c_int, wintypes.DWORD)
    g.BitBlt.restype = wintypes.BOOL
    g.CreateCompatibleBitmap.argtypes = (wintypes.HDC, ctypes.c_int, ctypes.c_int)
    g.CreateCompatibleBitmap.restype = wintypes.HBITMAP
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


def stable_window_identity(executable, classname, title):
    executable = str(executable or '').strip().casefold()
    classname = str(classname or '').strip().casefold()
    normalized_title = ' '.join(str(title or '').strip().casefold().split())
    normalized_title = re.sub(r'\s+(?:[-–—]\s*)?(?:google chrome|microsoft edge|mozilla firefox)\s*$', '', normalized_title)
    if executable:
        return executable + '|' + classname
    if classname and classname not in ('#32770', 'mainwindow', 'window', 'dialog'):
        return 'class|' + classname
    return 'title|' + normalized_title


def window_fingerprint(hwnd, title):
    identity = ' '.join(title.strip().casefold().split())
    if os.name != 'nt':
        return stable_window_identity('', '', identity)
    pid = wintypes.DWORD()
    if not u.GetWindowThreadProcessId(hwnd, ctypes.byref(pid)):
        return identity
    classname = ctypes.create_unicode_buffer(256)
    u.GetClassNameW(hwnd, classname, len(classname))
    kind = classname.value.casefold()
    browser = kind.startswith('chrome_widgetwin_') or kind == 'mozillawindowclass'
    process = kernel32.OpenProcess(0x1000, False, pid.value)
    if process:
        try:
            buf = ctypes.create_unicode_buffer(32768)
            size = wintypes.DWORD(len(buf))
            if kernel32.QueryFullProcessImageNameW(process, 0, buf, ctypes.byref(size)):
                executable = buf.value.casefold()
                return stable_window_identity(executable, kind, identity)
        finally:
            kernel32.CloseHandle(process)
    if browser:
        return stable_window_identity('browser', kind, identity)
    return stable_window_identity('', kind, identity)


def selected_data_folder():
    if os.name != 'nt':
        return None
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r'Software\WindowMouseAI') as entry:
            value, _ = winreg.QueryValueEx(entry, 'DataFolder')
        if isinstance(value, str) and value.strip() and Path(value).is_dir():
            return Path(value)
    except (OSError, ValueError, TypeError):
        pass
    return None


def persist_data_folder(folder):
    if os.name != 'nt':
        return
    try:
        import winreg
        with winreg.CreateKeyEx(winreg.HKEY_CURRENT_USER, r'Software\WindowMouseAI') as entry:
            winreg.SetValueEx(entry, 'DataFolder', 0, winreg.REG_SZ, str(folder))
    except (OSError, ValueError):
        pass


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


def associated_foreground_window(hwnd):
    if os.name != 'nt' or not hwnd or not u.IsWindow(hwnd):
        return None
    focused = u.GetForegroundWindow()
    if not focused:
        return None
    root = int(u.GetAncestor(focused, 2) or focused)
    if not u.IsWindow(root) or u.IsIconic(root) or not u.IsWindowVisible(root):
        return None
    original_pid = wintypes.DWORD()
    active_pid = wintypes.DWORD()
    if not u.GetWindowThreadProcessId(hwnd, ctypes.byref(original_pid)) or not u.GetWindowThreadProcessId(root, ctypes.byref(active_pid)):
        return None
    if original_pid.value == 0 or original_pid.value != active_pid.value:
        return None
    if root == int(hwnd):
        return root
    visited = set()
    owner = int(u.GetWindow(root, 4) or 0)
    while owner and owner not in visited and u.IsWindow(owner):
        visited.add(owner)
        if int(u.GetAncestor(owner, 2) or owner) == int(hwnd):
            return root
        owner = int(u.GetWindow(owner, 4) or 0)
    return None


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
        self.gdi_snapshot_region = None
        self.gdi_snapshot_dc = None
        self.gdi_snapshot_bitmap = None
        self.gdi_snapshot_old = None
        self.target_cache = ()
        self.target_scene = None
        self.demonstrated_element_atlas = None
        self.last_crop_region = None
        self.com_initialized = ole32.CoInitializeEx(None, 0) in (0, 1)
        self.io_lock = threading.RLock()
        self.keyboard_guard = None
        self.keyboard_heartbeat_guard = None
        self.human_guard = None
        self.user_override = threading.Event()
        self.input_generation = -1
        self.input_generation_guard = None
        self.exploration_targets = ()
        self.velocity = (0., 0.)
        self.motion_scale = 1.
        self.grabber = None
        self.grabber_errors = 0
        self.dxcam_retry_at = 0.
        self.dxcam_recovery_needed = False
        self.capture_failures = {'wgc': 0, 'dxcam': 0, 'gdi': 0}
        self.capture_quality = {name: {'mean_ms': 0., 'samples': 0, 'bad': 0} for name in ('wgc', 'dxcam', 'gdi')}
        self.capture_selected_at = 0.
        self.wgc_probe_at = 0.
        self.wgc_probe_frame_id = None
        self.scene_texture = None
        self.wgc = None
        self.wgc_control = None
        self.wgc_lock = threading.Lock()
        self.wgc_frame = None
        self.wgc_stamp = 0.
        self.wgc_frame_id = 0
        self.wgc_generation = 0
        self.wgc_closed = False
        self.wgc_shutdown = False
        self.last_frame_id = -1
        self.wgc_periods = deque(maxlen=96)
        self.post_action_capture = False
        self.capture_preference = 'auto'
        self.capture_recovery = ''
        self.last_capture_ms = 0.
        self.capture_epoch = 0
        self.last_frame_backend = None
        self.last_frame_valid = True
        self.last_frame_confirmed = False
        self.blank_frame_runs = 0
        self.last_capture_stamp = 0.
        self.last_input_sent_at = 0.
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
        self.pressed_at = {'l': None, 'r': None, 'm': None}
        self.scroll_credit = 0.
        self.last_ai_cursor = None
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
        now = time.monotonic()
        with self.wgc_lock:
            if self.wgc_shutdown:
                return False
            if self.wgc_control is not None and not self.wgc_closed:
                return True
            if now < self.wgc_retry_at:
                return False
            self.wgc_retry_at = now + max(2., math.sqrt(1. + self.capture_epoch))
            previous = self.wgc_control
            self.wgc_control = None
            self.wgc = None
            self.wgc_closed = False
            self.wgc_generation += 1
            generation = self.wgc_generation
            self.wgc_frame = None
            self.wgc_stamp = 0.
            self.wgc_frame_id += 1
        if previous is not None:
            try:
                previous.stop()
            except Exception:
                pass
        control = None
        try:
            windows_capture = importlib.import_module('windows_capture')
            interval_ms = max(1, round(self.display_period * 1000.)) if self.display_period else None
            source = windows_capture.WindowsCapture(window_hwnd=self.hwnd, cursor_capture=False, draw_border=False, minimum_update_interval=interval_ms)
            @source.event
            def on_frame_arrived(frame, capture_control):
                with self.wgc_lock:
                    if self.wgc_shutdown or generation != self.wgc_generation or self.wgc_closed:
                        return
                    current = time.monotonic()
                    if self.wgc_stamp and current > self.wgc_stamp:
                        self.wgc_periods.append(current - self.wgc_stamp)
                    self.wgc_frame = frame.frame_buffer.copy()
                    self.wgc_stamp = current
                    self.wgc_frame_id += 1
            @source.event
            def on_closed():
                with self.wgc_lock:
                    if self.wgc_shutdown or generation != self.wgc_generation:
                        return
                    self.wgc_closed = True
                    self.wgc_frame = None
                    self.wgc_stamp = 0.
                    self.wgc_frame_id += 1
                    self.capture_preference = 'dxcam' if self.grabber is not None else 'gdi'
                    self.capture_recovery = 'WGC 会话结束，已启用备用采集；准备自动重建 WGC'
            control = source.start_free_threaded()
            with self.wgc_lock:
                if not self.wgc_shutdown and generation == self.wgc_generation and not self.wgc_closed:
                    self.wgc = source
                    self.wgc_control = control
                    self.capture_preference = 'auto'
                    self.capture_epoch += 1
                    return True
            if control is not None:
                try:
                    control.stop()
                except Exception:
                    pass
            return False
        except Exception:
            if control is not None:
                try:
                    control.stop()
                except Exception:
                    pass
            with self.wgc_lock:
                if generation == self.wgc_generation:
                    self.wgc = None
                    self.wgc_control = None
                    self.wgc_closed = False
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

    def active_control_hwnd(self):
        pid = wintypes.DWORD()
        if (not u.IsWindow(self.hwnd) or not u.GetWindowThreadProcessId(self.hwnd, ctypes.byref(pid))
                or pid.value != self.window_pid.value):
            return None
        return associated_foreground_window(self.hwnd)

    def region(self):
        active = self.active_control_hwnd()
        if active is None:
            return None
        rect = RECT()
        if not u.GetClientRect(active, ctypes.byref(rect)):
            return None
        p = POINT(0, 0)
        if not u.ClientToScreen(active, ctypes.byref(p)):
            return None
        w, h = rect.right - rect.left, rect.bottom - rect.top
        if w < 8 or h < 8:
            return None
        return (p.x, p.y, w, h)

    def foreground(self):
        return self.active_control_hwnd() is not None

    def pointer_on_target(self, px, py):
        active = self.active_control_hwnd()
        if active is None:
            return False
        found = u.WindowFromPoint(POINT(px, py))
        if not found:
            return False
        return int(u.GetAncestor(found, 2) or found) == active

    def semantic_targets(self, region, frame=None, visual_points=()):
        now = time.monotonic()
        scene = session_signature(frame) if isinstance(frame, bytes) and len(frame) == VIS_N else None
        element_scene = element_scene_signature(frame) if scene is not None else None
        if self.target_region == region and now < self.target_scan_at:
            if scene == self.target_scene:
                return self.target_cache
            self.target_scene = scene
            self.target_cache = ()
            self.exploration_targets = ()
            return ()
        x, y, width, height = region
        found = []
        explorables = []
        def add_bounds(bounds, kind, quality, label='', role='other'):
            left, top, right, bottom = bounds
            left, right = max(x, left), min(x + width, right)
            top, bottom = max(y, top), min(y + height, bottom)
            if right <= left or bottom <= top:
                return
            center_x, center_y = (left + right) / 2, (top + bottom) / 2
            if not (x + 3 < center_x < x + width - 3 and y + 3 < center_y < y + height - 3):
                return
            if kind == 'scroll':
                found.append(((center_x - x) / width, (center_y - y) / height, max(.5, quality)))
                explorables.append((left, top, right, bottom, 'scroll'))
            else:
                authorized = (element_scene is not None and self.demonstrated_element_atlas is not None
                              and self.demonstrated_element_atlas.authorizes_element(
                                  element_scene, (label, role, bounds), (center_x, center_y), region))
                found.append(((center_x - x) / width, (center_y - y) / height,
                              max(.5, quality) + float(authorized)))
                explorables.append((left, top, right, bottom, 'click'))
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
                caption_buffer = ctypes.create_unicode_buffer(512)
                u.GetWindowTextW(child, caption_buffer, len(caption_buffer))
                role = ('link' if 'link' in category else 'tab' if 'tabcontrol' in category else
                        'button' if 'button' in category else 'other')
                kind = semantic_action(caption_buffer.value, role)
                if any(tag in category for tag in ('scrollbar', 'listbox', 'listview', 'treeview')):
                    kind = 'scroll'
                add_bounds((box.left, box.top, box.right, box.bottom), kind,
                           2. if kind == 'navigation' else 1., caption_buffer.value, role)
            except (OSError, ValueError, AttributeError):
                pass
            return True
        callback = WNDPROC(visit)
        active_window = self.active_control_hwnd()
        if active_window is not None:
            u.EnumChildWindows(active_window, callback, 0)
        if self.com_initialized:
            candidates_to_probe = [(int(x + width * point[0]), int(y + height * point[1])) for point in visual_points[:20]]
            candidates_to_probe.insert(0, self.cursor())
            seen_bounds = set()
            for point in candidates_to_probe:
                try:
                    if not self.pointer_on_target(*point):
                        continue
                    element = accessible_element_at(point)
                    if element is None:
                        continue
                    caption, role, bounds = element
                    if bounds is None or bounds in seen_bounds:
                        continue
                    seen_bounds.add(bounds)
                    kind = semantic_action(caption, role)
                    if role in ('button', 'link', 'tab', 'menu'):
                        add_bounds(bounds, kind, 3., caption, role)
                except (OSError, ValueError, RuntimeError, ctypes.ArgumentError):
                    continue
        self.target_cache = tuple(dict.fromkeys(found))
        self.exploration_targets = tuple(dict.fromkeys(explorables))
        self.target_region = region
        self.target_scene = scene
        self.target_scan_at = now + .35
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

    def verify_black_with_gdi(self, region):
        x, y, w, h = region
        if not g.StretchBlt(self.mem, 0, 0, VIS_W, VIS_H, self.src, x, y, w, h, 0x00CC0020):
            return None
        raw = ctypes.string_at(self.ptr, PIXELS * 4)
        return all(raw[channel::4].count(0) == PIXELS for channel in range(CHANNELS))

    def gdi_pair(self, region, crop):
        x, y, w, h = region
        cx, cy, cw, ch = crop
        if self.gdi_snapshot_region != (w, h):
            self.release_gdi_snapshot()
            dc = g.CreateCompatibleDC(self.src)
            if not dc:
                raise OSError('GDI 原始帧缓冲区创建失败')
            bitmap = g.CreateCompatibleBitmap(self.src, w, h)
            if not bitmap:
                g.DeleteDC(dc)
                raise OSError('GDI 原始帧位图创建失败')
            old = g.SelectObject(dc, bitmap)
            if not old:
                g.DeleteObject(bitmap)
                g.DeleteDC(dc)
                raise OSError('GDI 原始帧选择失败')
            self.gdi_snapshot_region = (w, h)
            self.gdi_snapshot_dc = dc
            self.gdi_snapshot_bitmap = bitmap
            self.gdi_snapshot_old = old
        if not g.BitBlt(self.gdi_snapshot_dc, 0, 0, w, h, self.src, x, y, 0x00CC0020):
            raise OSError('GDI 原始帧复制失败')
        stamp = time.monotonic()
        frames = []
        for src_x, src_y, src_w, src_h in ((0, 0, w, h), (cx - x, cy - y, cw, ch)):
            if not g.StretchBlt(self.mem, 0, 0, VIS_W, VIS_H, self.gdi_snapshot_dc,
                                src_x, src_y, src_w, src_h, 0x00CC0020):
                raise OSError('GDI 同帧双视野缩放失败')
            raw = ctypes.string_at(self.ptr, PIXELS * 4)
            frames.append(self.captured(raw[2::4] + raw[1::4] + raw[0::4], 'gdi', stamp))
        return b''.join(frames)

    def best_effort_gdi_pair(self, region, crop):
        try:
            return self.gdi_pair(region, crop)
        except (OSError, MemoryError):
            self.capture_recovery = '同帧GDI缓冲不可用，已降级为低置信度逐次采样'
            self.capture_metadata.clear()
            return self.capture(*region, force_gdi=True) + self.capture(*crop, force_gdi=True)

    def release_gdi_snapshot(self):
        if self.gdi_snapshot_dc is not None:
            if self.gdi_snapshot_old:
                g.SelectObject(self.gdi_snapshot_dc, self.gdi_snapshot_old)
            if self.gdi_snapshot_bitmap:
                g.DeleteObject(self.gdi_snapshot_bitmap)
            g.DeleteDC(self.gdi_snapshot_dc)
        self.gdi_snapshot_region = None
        self.gdi_snapshot_dc = None
        self.gdi_snapshot_bitmap = None
        self.gdi_snapshot_old = None

    def dxcam_ready(self):
        return (self.grabber is not None and time.monotonic() >= self.dxcam_retry_at and
                (self.capture_preference != 'gdi' or self.dxcam_recovery_needed))

    def dxcam_failed(self):
        self.grabber_errors += 1
        self.dxcam_recovery_needed = True
        self.dxcam_retry_at = time.monotonic() + min(60., 2. ** min(self.grabber_errors, 6))

    def dxcam_succeeded(self):
        self.grabber_errors = 0
        self.dxcam_retry_at = 0.
        if self.dxcam_recovery_needed and self.capture_preference == 'gdi':
            self.capture_preference = 'dxcam'
            self.capture_selected_at = time.monotonic()
            self.capture_recovery = 'DXCAM 已通过重新采样验证，恢复 GPU 截图后端'
        self.dxcam_recovery_needed = False

    def capture(self, x, y, w, h, force_gdi=False):
        if (not force_gdi and self.capture_preference == 'auto' and self.wgc is not None
                and not self.wgc_closed and self.active_control_hwnd() == self.hwnd):
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
        if not force_gdi and self.dxcam_ready():
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
                if image is None or len(image.shape) != 3 or image.shape[2] < 3:
                    raise RuntimeError('DXCAM 未取得完整画面')
                result = self.resample(image)
                self.dxcam_succeeded()
                return self.captured(result, 'dxcam', stamp)
            except Exception:
                self.dxcam_failed()
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
        if self.capture_preference != 'auto' and self.wgc is not None and not self.wgc_closed:
            with self.wgc_lock:
                stamp = self.wgc_stamp
                frame_id = self.wgc_frame_id
                recent = tuple(self.wgc_periods)
            period = sorted(recent)[int(.9 * (len(recent) - 1))] if recent else self.display_period
            probe_gap = max(3., 24. * max(period, self.last_capture_ms / 1000., .01))
            if (stamp and (self.wgc_probe_frame_id is None or frame_id > self.wgc_probe_frame_id)
                    and capture_start - stamp < max(period * 2., self.display_period, .05)
                    and capture_start - self.wgc_probe_at >= probe_gap):
                self.wgc_probe_at = capture_start
                self.capture_preference = 'auto'
                testing_wgc = True
        self.capture_metadata = []
        self.frozen_dxcam = None
        x, y, w, h = region
        px, py = self.cursor()
        with self.wgc_lock:
            self.frozen_wgc = (self.wgc_frame, self.wgc_stamp, self.wgc_frame_id)
            recent_wgc_periods = tuple(self.wgc_periods)
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
                self.scene_texture += (texture - self.scene_texture) / max(1., math.sqrt(1. + self.capture_epoch + len(recent_wgc_periods)))
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
            crop = (crop_x, crop_y, zoom_w, zoom_h)
            if self.capture_metadata and self.capture_metadata[0][0] == 'gdi':
                self.capture_metadata.clear()
                result = self.best_effort_gdi_pair(region, crop)
            else:
                result = overview + self.capture(*crop)
                if len(self.capture_metadata) != 2 or self.capture_metadata[0][0] != self.capture_metadata[1][0]:
                    self.capture_metadata.clear()
                    result = self.best_effort_gdi_pair(region, crop)
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
        self.last_frame_confirmed = (backend == 'wgc' and self.last_frame_id >= 0 or
                                     backend == 'dxcam' and self.post_action_capture and len(self.capture_metadata) == 2)
        if backend == 'gdi':
            self.last_frame_confirmed = False
        if len(result) == VIS_N:
            blank = result.count(0) == VIS_N
            self.blank_frame_runs = self.blank_frame_runs + 1 if blank else 0
            if self.blank_frame_runs >= 3:
                if backend in ('wgc', 'dxcam'):
                    comparison = self.verify_black_with_gdi(region)
                    if comparison is not True:
                        self.last_frame_valid = False
                        self.capture_preference = 'gdi'
                        self.capture_selected_at = capture_start
                        self.capture_recovery = '黑色画面未通过独立 GDI 复核，切换采集源并暂停操作'
                    else:
                        self.capture_recovery = '多采集源均确认黑色画面，按有效暗色场景处理'
                else:
                    self.capture_recovery = 'GDI 捕获黑色画面；未仅因黑色像素拒绝画面'
        if backend == 'wgc' and self.last_frame_valid:
            self.wgc_probe_frame_id = None
        if backend == 'gdi' and len(self.capture_metadata) == 2:
            self.last_frame_valid = self.last_frame_valid and all(stamp >= capture_start for _, stamp, _ in self.capture_metadata)
        if backend == 'dxcam' and len(self.capture_metadata) == 2 and self.capture_metadata[0][1] != self.capture_metadata[1][1]:
            self.last_frame_valid = False
        if backend != self.last_frame_backend:
            self.capture_epoch += 1
            self.last_frame_backend = backend
        self.last_capture_stamp = min((stamp for _, stamp, _ in self.capture_metadata), default=0.)
        recent_periods = sorted(recent_wgc_periods)
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
                if data['samples'] < 3 or mode == 'dxcam' and self.grabber is None or mode == 'wgc' and (self.wgc is None or self.wgc_closed):
                    continue
                if mode == 'wgc' and self.wgc_probe_frame_id is not None:
                    with self.wgc_lock:
                        if self.wgc_frame_id <= self.wgc_probe_frame_id:
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
        self.last_frame_confirmed = self.last_frame_confirmed and self.last_frame_valid
        self.last_crop_region = crop if self.last_frame_valid else None
        return result

    def fresh_image(self, region, action_finished, expected_epoch, stop, action_started=None):
        with self.wgc_lock:
            recent = sorted(self.wgc_periods)
        period = recent[min(len(recent) - 1, int(len(recent) * .9))] if recent else max(self.display_period, self.last_capture_ms / 1000., sys.float_info.epsilon)
        capture_cost = self.last_capture_ms / 1000.
        jitter = (recent[-1] - recent[0]) if len(recent) > 1 else 0.
        budget = max(2. * period + jitter, 2. * capture_cost + period, self.display_period)
        deadline = action_finished + budget
        initial_id = self.last_frame_id
        earliest_fallback = action_finished + (self.display_period or period)
        action_started = action_finished if action_started is None else action_started
        input_started = max(action_started, self.last_input_sent_at)
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
                    fresh = self.last_frame_id >= 0 and self.last_frame_id != initial_id and self.last_capture_stamp >= input_started
                elif self.last_frame_backend == 'dxcam':
                    fresh = self.last_capture_stamp >= action_finished
                else:
                    fresh = captured_after >= earliest_fallback and self.last_capture_stamp >= action_finished
                if self.last_frame_valid and fresh:
                    self.last_frame_confirmed = self.last_frame_backend in ('wgc', 'dxcam')
                    return frame
                if time.monotonic() >= deadline:
                    if self.last_frame_backend == 'wgc':
                        with self.wgc_lock:
                            self.wgc_probe_frame_id = self.wgc_frame_id
                        self.capture_preference = 'gdi'
                        self.capture_selected_at = time.monotonic()
                        self.capture_recovery = f'WGC 在 {budget:.2f}s 内没有动作后新帧，改用同步 GDI 截图复核静态画面'
                    elif self.last_frame_backend == 'dxcam':
                        self.dxcam_failed()
                        self.capture_preference = 'gdi'
                        self.capture_selected_at = time.monotonic()
                        self.capture_recovery = 'DXCAM 无法确认动作后新画面，已改用 GDI 连续采集并计划重试'
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
        if self.release_uncertain:
            raise RuntimeError('上次鼠标释放结果尚未确认，禁止下一动作')
        if ((self.keyboard_guard is not None and not self.keyboard_guard.is_set()) or
                (self.keyboard_heartbeat_guard is not None and not self.keyboard_heartbeat_guard())):
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
            self.last_input_sent_at = time.monotonic()
            send_mouse(flags[name][0 if press else 1], stop=self.input_stop(stop) if stop is not None else self.input_stop(self.halted))
            self.down[name] = press
            self.pressed_at[name] = time.monotonic() if press else None
            self.release_uncertain = False
            return True

    def stale_button(self):
        now = time.monotonic()
        held = [(stamp, name) for name, stamp in self.pressed_at.items()
                if stamp is not None and self.down[name] and now - stamp >= BUTTON_STALE_TIMEOUT]
        return min(held)[1] if held else None

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
                    self.pressed_at[name] = None
                except OSError as error:
                    failure = error
            self.release_uncertain = failure is not None
            self.velocity = (0., 0.)
            if failure is not None:
                raise RuntimeError('AI 已按下的鼠标键释放未全部确认') from failure

    def interrupt_release(self, permanent=False):
        if permanent:
            self.halted.set()
        self.release_uncertain = True
        for flag in (4, 16, 64):
            try:
                send_mouse(flag)
            except OSError:
                pass
        self.quick_release()

    def release(self):
        self.quick_release()

    def halt(self):
        self.interrupt_release(permanent=True)

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
                self.last_input_sent_at = time.monotonic()
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
            if wheel:
                period = self.display_period or max(dt, self.last_capture_ms / 1000., time.get_clock_info('monotonic').resolution)
                self.scroll_credit = max(-1., min(1., self.scroll_credit + wheel * dt / period))
                if abs(self.scroll_credit) >= 1.:
                    self.safe(region, stop)
                    delta = 120 if self.scroll_credit > 0. else -120
                    self.last_input_sent_at = time.monotonic()
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
        with self.wgc_lock:
            self.wgc_shutdown = True
            self.wgc_generation += 1
            control = self.wgc_control
            self.wgc_control = None
            self.wgc = None
            self.wgc_frame = None
            self.frozen_wgc = None
        if control is not None:
            try:
                control.stop()
            except Exception:
                pass
        if self.grabber is not None:
            try:
                self.grabber.stop()
                if hasattr(self.grabber, 'release'):
                    self.grabber.release()
            except (AttributeError, OSError, RuntimeError):
                pass
            finally:
                self.grabber = None
        self.release_gdi_snapshot()
        if getattr(self, 'old', None):
            g.SelectObject(self.mem, self.old)
        if getattr(self, 'bmp', None):
            g.DeleteObject(self.bmp)
        if getattr(self, 'mem', None):
            g.DeleteDC(self.mem)
        if getattr(self, 'src', None):
            u.ReleaseDC(None, self.src)
        if self.com_initialized:
            ole32.CoUninitialize()
            self.com_initialized = False
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
    env = runtime_environment(folder)
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
    (runtime_folder / '.cache').mkdir(parents=True, exist_ok=True)
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
                ready = RemoteBrain(folder, runtime, backend, cancel, cache_folder=runtime_folder)
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
            return RemoteBrain(folder, runtime, 'cpu', cancel, cache_folder=runtime_folder)
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
                    ready = RemoteBrain(folder, cpu_runtime, 'cpu', cancel, cache_folder=runtime_folder)
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
        enable_numpy_acceleration()
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
            enable_numpy_acceleration()
            return
        except (ImportError, OSError, RuntimeError):
            pass
    if not installation_due(folder, 'capture_' + python_runtime_id()):
        return
    started = time.monotonic()
    installed = False
    try:
        if install_package(folder, ['windows-capture', 'numpy'], report, cancel, 'capture'):
            if str(runtime) not in sys.path:
                sys.path.insert(0, str(runtime))
            importlib.invalidate_caches()
            importlib.import_module('windows_capture')
            enable_numpy_acceleration()
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
        self.root.geometry(f'{work_width}x{work_height}')
        self.root.minsize(min(720, work_width), min(460, work_height))
        if os.name == 'nt':
            try:
                self.root.state('zoomed')
            except tk.TclError:
                pass
        home = Path.home()
        suggested_folder = (home / 'Documents' / 'MouseAI') if (home / 'Documents').exists() else (home / 'MouseAI')
        stored_folder = selected_data_folder()
        self.folder = stored_folder if stored_folder is not None else suggested_folder
        self.folder_selected = stored_folder is not None
        self.hardware_probe_thread = None
        self.control_stop = threading.Event()
        self.observer_stop = threading.Event()
        self.human_lock = threading.RLock()
        self.user_override = threading.Event()
        self.user_override.set()
        self.takeover_permission = threading.Event()
        self.takeover_window = None
        self.explore_permission = threading.Event()
        self.human_last_input = time.monotonic()
        self.human_gaps = deque(maxlen=256)
        self.human_events = deque(maxlen=4096)
        self.human_event_id = 0
        self.observed_count = 0
        self.session_hwnd = None
        self.pending_folder = None
        self.next_observer_retry = 0.
        self.last_activation_attempt_at = 0.
        self.handoff_pending = False
        self.manual_start_pending = False
        self.control_lease_active = False
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
        self.keyboard_event_signal = threading.Event()
        self.hook_event_lock = threading.Lock()
        self.hook_mouse_events = deque(maxlen=8192)
        self.ai_mouse_attribution = Counter()
        self.keyboard_alive_at = 0.
        self.safety_alive_at = 0.
        self.start_queued = None
        self.control_worker = None
        self.control_heartbeat = 0.
        self.watchdog_limit = 18.
        self.inference_deadline = 0.
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
        self.retired_workers = set()
        self.retired_lock = threading.Lock()
        self.exit_backup_error = None
        self.last_checkpoint_step = 0
        self.last_checkpoint_time = time.monotonic()
        self.last_checkpoint_duration = 0.
        self.consolidated_steps = {}
        self.consolidation_at = 0.
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
        self.folder_text = tk.StringVar(value=str(self.folder) if self.folder_selected else '尚未选择数据目录（需手动选择一次）')
        self.status = tk.StringVar(value='先选择数据目录和目标窗口；已授权后自动学习、接管，按键立即停控')
        self.phase = tk.StringVar(value='空闲')
        self.progress_value = tk.DoubleVar(value=0.)
        self.progress_text = tk.StringVar(value='准备状态 · 0%')
        self.issue = tk.StringVar(value='无')
        self.statistics = tk.StringVar(value='经验 0 条 · 实际操作 0 次 · 可控进展待观测（非任务成功率）')
        self.learning_summary = tk.StringVar(value='学习：暂无经验 · 进展尚待观测')
        self.consolidation_status = tk.StringVar(value='自动巩固：等待足量独立训练、验证和审计经验')
        self.capture_text = tk.StringVar(value=f'视觉输入 {VIS_W}×{VIS_H} 双视野 · 客户区与局部视野自动取样 · 总像素 {PIXELS * 2:,}')
        self.goal_text = tk.StringVar(value='等待观察 · 尚未建立状态目标')
        self.metric_text = tk.StringVar(value='诊断指标会自动轮播，无需操作')
        self.metric_pages = ()
        self.stat_pages = ()
        self.metric_page = 0
        self.metric_rotate_at = time.monotonic() + 6.
        self.safety_text = tk.StringVar(value='键盘急停监控正在启动')
        self.fps_text = tk.StringVar(value='控制 FPS：尚未测量')
        self.gpu_state = tk.StringVar(value='GPU：正在识别硬件 · 尚未验证训练')
        self.storage_state = tk.StringVar(value='存储：等待选择数据目录' if not self.folder_selected else '存储：数据目录已授权')
        self.checkpoint_status = tk.StringVar(value='检查点：等待首个成功保存')
        self.control_details = tk.StringVar(value='鼠标未控制 · 左键释放 · 右键释放 · 中键释放 · 滚轮停止')
        self.combo_var = tk.StringVar()
        self.environment_code = (0., 0.)
        self.data_folder = self.folder
        self.audit_sum = 0.
        self.audit_samples = 0
        self.preview_at = 0.
        self.preview_photos = []
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
        self.ui_font = tkfont.Font(family='Microsoft YaHei UI', size=9)
        self.ui_bold = tkfont.Font(family='Microsoft YaHei UI', size=9, weight='bold')
        self.ui_title = tkfont.Font(family='Microsoft YaHei UI', size=16, weight='bold')
        sty = ttk.Style(self.root)
        try:
            sty.theme_use('clam')
        except tk.TclError:
            pass
        sty.configure('AI.TCombobox', font=self.ui_font, padding=4)
        top = tk.Frame(self.root, bg='#10131a')
        top.pack(fill='x', padx=12, pady=(7, 3))
        tk.Label(top, text='窗口鼠标 AI', bg='#10131a', fg='#f2f5fa', font=self.ui_title).pack(side='left', padx=(0, 15))
        tk.Label(top, text='目标窗口', bg='#10131a', fg='#d9e0ea', font=self.ui_font).pack(side='left', padx=(0, 7))
        self.combo = ttk.Combobox(top, textvariable=self.combo_var, state='readonly', style='AI.TCombobox', font=self.ui_font)
        self.combo.pack(side='left', fill='x', expand=True)
        self.combo.bind('<<ComboboxSelected>>', self.preload_selected)
        tk.Button(top, text='刷新', command=self.refresh, bg='#303949', fg='white', relief='flat', cursor='hand2', font=self.ui_font, padx=10, pady=4).pack(side='left', padx=(7, 0))
        self.start_button = tk.Button(top, text='开始 AI 控制', command=self.request_start, bg='#168449', activebackground='#20a35c', fg='white', activeforeground='white', relief='flat', cursor='hand2', font=self.ui_bold, padx=13, pady=4)
        self.start_button.pack(side='left', padx=(9, 0))
        self.notice = tk.Label(self.root, text='选择数据文件夹和目标窗口后，点击绿色按钮启动 · 仅对所选窗口操作 · 任意键盘输入立即停止 · 真实鼠标输入优先', bg='#10131a', fg='#9de1d5', anchor='w', justify='left', font=self.ui_font)
        self.notice.pack(fill='x', padx=12, pady=(1, 4))
        lower = tk.Frame(self.root, bg='#10131a')
        lower.pack(side='bottom', fill='x', padx=12, pady=(3, 6))
        self.folder_button = tk.Button(lower, text='选择数据文件夹', command=self.choose_folder, bg='#303949', fg='#f5f7fa', relief='flat', padx=9, pady=4, cursor='hand2', font=self.ui_font)
        self.folder_button.pack(side='left')
        self.folder_label = tk.Label(lower, textvariable=self.folder_text, bg='#10131a', fg='#a9b6c8', anchor='w', justify='left', font=self.ui_font)
        self.folder_label.pack(side='left', fill='x', expand=True, padx=(8, 0))
        surface = tk.Frame(self.root, bg='#10131a')
        surface.pack(fill='both', expand=True, padx=12, pady=(0, 3))
        surface.columnconfigure(0, weight=11, uniform='layout')
        surface.columnconfigure(1, weight=9, uniform='layout')
        surface.rowconfigure(0, weight=1)
        dashboard = tk.Frame(surface, bg='#202631', padx=10, pady=7)
        dashboard.grid(row=0, column=0, sticky='nsew', padx=(0, 4))
        heading = tk.Frame(dashboard, bg='#202631')
        heading.pack(fill='x')
        tk.Label(heading, text='当前阶段', bg='#202631', fg='#9aaac0', font=self.ui_font).pack(side='left')
        tk.Label(heading, textvariable=self.phase, bg='#202631', fg='#69cfbd', font=self.ui_bold).pack(side='left', padx=(8, 12))
        tk.Label(heading, textvariable=self.fps_text, bg='#202631', fg='#69cfbd', font=self.ui_bold).pack(side='left')
        self.overview_labels = []
        for var, color in ((self.backend, '#9de1d5'), (self.gpu_state, '#9de1d5'),
                           (self.checkpoint_status, '#b0c0d4'), (self.safety_text, '#ffbb85'),
                           (self.issue, '#ffbb85'), (self.status, '#e0e8f2')):
            label = tk.Label(dashboard, textvariable=var, bg='#202631', fg=color, font=self.ui_font,
                             anchor='w', justify='left', wraplength=500)
            label.pack(fill='x', pady=(3, 1))
            self.overview_labels.append(label)
        self.rotating_overview = (self.capture_text, self.storage_state, self.learning_summary,
                                  self.consolidation_status)
        self.rotating_overview_labels = []
        self.overview_page = 0
        for index in range(2):
            label = tk.Label(dashboard, textvariable=self.rotating_overview[index], bg='#202631',
                             fg='#b0c0d4', font=self.ui_font, anchor='w', justify='left', wraplength=500)
            label.pack(fill='x', pady=(3, 1))
            self.overview_labels.append(label)
            self.rotating_overview_labels.append(label)
        self.root.after(6500, self.rotate_overview)
        progress_row = tk.Frame(dashboard, bg='#202631')
        progress_row.pack(fill='x', pady=(7, 2))
        tk.Label(progress_row, text='当前任务进度', bg='#202631', fg='#9aaac0', font=self.ui_font).pack(side='left')
        tk.Label(progress_row, textvariable=self.progress_text, bg='#202631', fg='#69cfbd', font=self.ui_font).pack(side='right')
        sty.configure('AI.Horizontal.TProgressbar', troughcolor='#10131a', background='#18ad65', borderwidth=0, thickness=9)
        self.progress_bar = ttk.Progressbar(dashboard, variable=self.progress_value, maximum=100, mode='determinate', style='AI.Horizontal.TProgressbar')
        self.progress_bar.pack(fill='x')
        detail_side = tk.Frame(surface, bg='#202631', padx=10, pady=7)
        detail_side.grid(row=0, column=1, sticky='nsew', padx=(4, 0))
        tk.Label(detail_side, text='实时画面', bg='#202631', fg='#d7e6ff', anchor='w', font=self.ui_bold).pack(fill='x')
        previews = tk.Frame(detail_side, bg='#202631')
        previews.pack(fill='x', pady=(5, 8))
        self.preview_frame = previews
        self.preview_labels = []
        for i, name in enumerate(('全窗口概览', '鼠标附近细节')):
            item = tk.Frame(previews, bg='#202631')
            item.grid(row=0, column=i, sticky='new', padx=(0, 4) if i == 0 else (4, 0))
            previews.columnconfigure(i, weight=1, uniform='preview')
            tk.Label(item, text=name, bg='#202631', fg='#9aaac0', anchor='w', font=self.ui_font).pack(fill='x')
            visual = tk.Label(item, text='等待首帧', bg='#141923', fg='#74849b', font=self.ui_font, height=3)
            visual.pack(fill='x')
            visual.bind('<Button-1>', lambda event, view=i: self.enlarge_preview(view))
            visual.configure(cursor='hand2')
            self.preview_labels.append(visual)
        tk.Label(detail_side, text='学习与采集详情', bg='#202631', fg='#d7e6ff', anchor='w', font=self.ui_bold).pack(fill='x', pady=(0, 3))
        detail_grid = tk.Frame(detail_side, bg='#202631')
        detail_grid.pack(fill='x')
        detail_grid.columnconfigure(0, weight=1, uniform='detail')
        detail_grid.columnconfigure(1, weight=1, uniform='detail')
        self.detail_labels = []
        for index, (label, var, color) in enumerate((('鼠标动作', self.control_details, '#d7e6ff'), ('学习情况', self.statistics, '#b0c0d4'), ('自主目标', self.goal_text, '#69cfbd'))):
            block = tk.Frame(detail_grid, bg='#202631')
            block.grid(row=index // 2, column=index % 2, sticky='nsew', padx=(0, 6), pady=(3, 5))
            tk.Label(block, text=label, bg='#202631', fg='#8c9bb0', anchor='w', font=self.ui_bold).pack(fill='x')
            value = tk.Label(block, textvariable=var, bg='#202631', fg=color, anchor='w', justify='left', font=self.ui_font, wraplength=200)
            value.pack(fill='x')
            self.detail_labels.append(value)
        self.metric_label = tk.Label(detail_side, textvariable=self.metric_text, bg='#202631',
                                     fg='#aec9e9', anchor='w', justify='left', font=self.ui_font,
                                     wraplength=500)
        self.metric_label.pack(fill='x', pady=(5, 2))
        self.latest_preview = None
        def resize_layout(event=None):
            width = max(1, dashboard.winfo_width() - 22)
            self.notice.configure(wraplength=max(240, self.root.winfo_width() - 24))
            self.folder_label.configure(wraplength=max(200, self.root.winfo_width() - self.folder_button.winfo_width() - 44))
            for label in self.overview_labels:
                label.configure(wraplength=width)
            detail_width = max(160, (detail_side.winfo_width() - 44) // 2)
            for label in self.detail_labels:
                label.configure(wraplength=detail_width)
            self.metric_label.configure(wraplength=max(160, detail_side.winfo_width() - 22))
            if self.latest_preview is not None:
                image_width = previews.winfo_width()
                if getattr(self, '_preview_width', None) != image_width:
                    self._preview_width = image_width
                    self.root.after_idle(lambda: self.render_preview(self.latest_preview))
        dashboard.bind('<Configure>', resize_layout)
        detail_side.bind('<Configure>', resize_layout)
        detail_grid.bind('<Configure>', resize_layout)
        previews.bind('<Configure>', resize_layout)
        self.root.after_idle(resize_layout)
        self.hud = None
        self.hud_text = None
        if os.name == 'nt':
            self.create_hud()

    def create_hud(self):
        hud = None
        try:
            hud = tk.Toplevel(self.root)
            hud.withdraw()
            hud.overrideredirect(True)
            hud.configure(bg='#10131a')
            hud.attributes('-topmost', True)
            hud.attributes('-disabled', True)
            summary = tk.StringVar(value='')
            tk.Label(hud, textvariable=summary, bg='#10131a', fg='#e0efff', font=self.ui_font,
                     justify='left', anchor='w', wraplength=410, padx=12, pady=9).pack(fill='both')
            hud.update_idletasks()
            hwnd = int(u.GetAncestor(hud.winfo_id(), 2) or hud.winfo_id())
            user32 = ctypes.WinDLL('user32', use_last_error=True)
            user32.GetWindowLongPtrW.argtypes = (wintypes.HWND, ctypes.c_int)
            user32.GetWindowLongPtrW.restype = ctypes.c_ssize_t
            user32.SetWindowLongPtrW.argtypes = (wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t)
            user32.SetWindowLongPtrW.restype = ctypes.c_ssize_t
            user32.SetWindowDisplayAffinity.argtypes = (wintypes.HWND, wintypes.DWORD)
            user32.SetWindowDisplayAffinity.restype = wintypes.BOOL
            style = user32.GetWindowLongPtrW(hwnd, -20)
            required = 0x08000000 | 0x00000080 | 0x00000020
            user32.SetWindowLongPtrW(hwnd, -20, style | required)
            if (user32.GetWindowLongPtrW(hwnd, -20) & required) != required:
                raise OSError('悬浮监控的无焦点属性不可用')
            if not user32.SetWindowDisplayAffinity(hwnd, 0x11):
                raise OSError('悬浮监控无法排除截图')
            width = 430
            left = max(0, self.root.winfo_screenwidth() - width - 16)
            hud.geometry(f'{width}x210+{left}+12')
            self.hud = hud
            self.hud_text = summary
        except (OSError, AttributeError, ValueError, tk.TclError):
            if hud is not None:
                try:
                    hud.destroy()
                except tk.TclError:
                    pass

    def update_hud(self):
        if self.hud is None or self.exit_stop.is_set():
            return
        try:
            if self.mode != 'control':
                self.hud.withdraw()
                return
            summary = ('窗口鼠标 AI · ' + self.control_state + '\n' +
                       self.fps_text.get() + '\n' +
                       self.backend.get()[:72] + '\n' +
                       self.gpu_state.get()[:92] + '\n' +
                       self.control_details.get()[:105] + '\n' +
                       self.goal_text.get()[:80] + '\n' +
                       self.metric_text.get()[:115] + '\n' +
                       self.safety_text.get()[:100])
            self.hud_text.set(summary)
            if self.hud.state() == 'withdrawn':
                self.hud.deiconify()
        except tk.TclError:
            self.hud = None
            self.hud_text = None

    def rotate_overview(self):
        if self.exit_stop.is_set():
            return
        self.overview_page = (self.overview_page + 2) % len(self.rotating_overview)
        for offset, label in enumerate(self.rotating_overview_labels):
            label.configure(textvariable=self.rotating_overview[(self.overview_page + offset) % len(self.rotating_overview)])
        self.root.after(6500, self.rotate_overview)

    def report_storage(self):
        if self.exit_stop.is_set():
            return
        if not self.folder_selected:
            self.storage_state.set('存储：等待用户选择数据文件夹')
            self.root.after(3000, self.report_storage)
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

    def activate_selected_window(self, hwnd):
        if self.exit_stop.is_set() or self.listing.get(self.combo_var.get()) != hwnd or os.name != 'nt':
            return
        now = time.monotonic()
        if now - self.last_activation_attempt_at < .7:
            return
        self.last_activation_attempt_at = now
        try:
            if not u.IsWindow(hwnd):
                return
            if associated_foreground_window(hwnd) is not None:
                return
            if u.IsIconic(hwnd):
                u.ShowWindow(hwnd, 9)
            if not u.SetForegroundWindow(hwnd):
                self.post('status', 'Windows 未立即允许激活目标窗口，正在等待合适时机重试')
        except (OSError, ValueError) as error:
            self.post('status', '目标窗口自动激活失败：' + str(error)[:85])

    def input_generation_current(self, generation):
        with self.human_lock:
            return self.human_event_id == generation and not self.user_override.is_set()

    def revoke_takeover_permission(self):
        self.takeover_permission.clear()
        self.explore_permission.clear()
        self.takeover_window = None
        self.manual_start_pending = False
        self.control_lease_active = False
        self.handoff_pending = False
        self.start_queued = None
        if self.mode == 'control':
            self.emergency_stop('目标窗口或数据目录已变化，马上释放鼠标')

    def preload_selected(self, event=None):
        if not self.folder_selected:
            self.status.set('请先点击“选择数据文件夹”；授权完成后无需额外配置')
            return
        selected_window = self.listing.get(self.combo_var.get())
        if self.takeover_window != selected_window:
            self.revoke_takeover_permission()
        self.human_input()
        self.task_failed = False
        self.status.set('已选择目标窗口，观察学习自动开始；点击绿色按钮才会启用自主鼠标控制')
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

    def transition_control(self, state):
        if state not in ('空闲', '准备中', '控制中', '安全暂停', '已停止'):
            raise ValueError('无效的鼠标控制状态')
        with self.human_lock:
            if state == '控制中' and (self.control_stop.is_set() or self.user_override.is_set() or
                                      self.keyboard_stopped_control.is_set() or not self.keyboard_healthy()):
                raise InterruptedError('输入许可已经撤销，禁止进入鼠标控制状态')
            self.control_state = state
            if state == '控制中':
                self.manual_start_pending = False
                self.control_lease_active = not self.user_override.is_set()
            elif state in ('安全暂停', '已停止', '空闲'):
                self.control_lease_active = False
            if state in ('安全暂停', '已停止', '空闲'):
                self.mouse_monitor_armed.clear()
                self.control_heartbeat = 0.

    def human_input(self, mouse_event=None, keyboard=False, stamp=None):
        now = time.monotonic() if stamp is None else float(stamp)
        with self.human_lock:
            self.user_override.set()
            self.control_lease_active = False
            elapsed = now - self.human_last_input
            if elapsed > (float(u.GetDoubleClickTime()) / 1000. if os.name == 'nt' else .5):
                self.human_gaps.append(elapsed)
            self.human_last_input = max(self.human_last_input, now)
            self.human_event_id += 1
            if mouse_event is not None:
                self.human_events.append((self.human_event_id, now, *mouse_event))
        if keyboard and self.manual_start_pending:
            self.keyboard_stopped_control.set()
            self.control_stop.set()
            self.revoke_takeover_permission()
        if self.mode == 'control' and not self.control_stop.is_set():
            self.mouse_monitor_armed.clear()
            self.release_signal.set()
            if keyboard:
                self.keyboard_stopped_control.set()
                self.emergency_stop('检测到真实键盘输入，已停止鼠标控制', fast=True)
            else:
                self.transition_control('安全暂停')
                self.control_heartbeat = 0.

    def idle_delay(self):
        double_click = float(u.GetDoubleClickTime()) / 1000. if os.name == 'nt' else .5
        baseline = max(5., double_click * 6., time.get_clock_info('monotonic').resolution)
        with self.human_lock:
            gaps = sorted(g for g in self.human_gaps if g > double_click)
        if len(gaps) < max(4, math.isqrt(self.human_gaps.maxlen)):
            return baseline
        center = gaps[len(gaps) // 2]
        deviation = sorted(abs(value - center) for value in gaps)[len(gaps) // 2]
        typical_pause = center + 2. * deviation
        return max(baseline, min(typical_pause, gaps[int(.9 * (len(gaps) - 1))]))

    def human_idle(self):
        with self.human_lock:
            if (self.takeover_permission.is_set() and
                    (self.control_lease_active or self.manual_start_pending) and
                    not self.user_override.is_set() and
                    not self.keyboard_stopped_control.is_set()):
                return True
            last = self.human_last_input
        timeout = self.idle_delay()
        if time.monotonic() - last < timeout:
            return False
        if self.mode != 'control':
            observed = system_idle_seconds()
            if observed is None or observed < timeout:
                return False
        return True

    def keyboard_healthy(self):
        now = time.monotonic()
        return (self.keyboard_ready.is_set() and self.key_thread is not None and self.key_thread.is_alive() and
                self.safety_thread is not None and self.safety_thread.is_alive() and
                self.keyboard_alive_at > 0. and self.safety_alive_at > 0. and
                0. <= now - self.keyboard_alive_at < KEYBOARD_HEARTBEAT_TIMEOUT and
                0. <= now - self.safety_alive_at < KEYBOARD_HEARTBEAT_TIMEOUT)

    def takeover_allowed(self):
        manual = self.manual_start_pending and self.takeover_permission.is_set()
        leased = self.mode == 'control' and self.control_lease_active and not self.user_override.is_set()
        if (not self.folder_selected or os.name != 'nt' or self.keyboard_stopped_control.is_set() or
                (self.active_io is not None and self.active_io.release_uncertain) or
                not self.takeover_permission.is_set() or self.takeover_window != self.session_hwnd or
                self.keyboard_event_signal.is_set() or not self.keyboard_healthy() or
                (not manual and not leased and not self.human_idle())):
            return False
        try:
            autonomous_mouse = self.mode == 'control' and self.control_state == '控制中'
            tracked = self.active_io.down if self.mode == 'control' and self.active_io is not None else {}
            eligible = (interactive_desktop() and associated_foreground_window(self.session_hwnd) is not None and
                        (autonomous_mouse or not any(u.GetAsyncKeyState(vk) & 0x8000 for name, vk in (('l', 1), ('r', 2), ('m', 4)) if not tracked.get(name, False))) and
                        (autonomous_mouse or not any(u.GetAsyncKeyState(vk) & 0x8000 for vk in (5, 6))) and
                        not any(u.GetAsyncKeyState(vk) & 0x8000 for vk in range(7, 256)))
            if not eligible:
                return False
            with self.human_lock:
                if not (manual or leased):
                    delay = self.idle_delay()
                    if time.monotonic() - self.human_last_input < delay:
                        return False
                    if self.mode != 'control':
                        system_idle = system_idle_seconds()
                        if system_idle is None or system_idle < delay:
                            return False
                elif manual and time.monotonic() - self.human_last_input < .12:
                    return False
                if (self.keyboard_stopped_control.is_set() or not self.keyboard_healthy() or
                        self.control_stop.is_set() or self.exit_stop.is_set() or
                        self.keyboard_event_signal.is_set()):
                    return False
                with self.hook_event_lock:
                    if self.hook_mouse_events:
                        return False
                self.user_override.clear()
                if self.active_io is not None:
                    self.active_io.input_generation = self.human_event_id
                return True
        except (OSError, ValueError, AttributeError):
            return False

    def begin_observing(self):
        if not self.folder_selected or self.exit_stop.is_set() or self.switching_folder or self.pending_folder is not None or self.manual_start_pending:
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
        pending_click = None
        idle_reference = None
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
                    pending_click = None
                    idle_reference = None
                    announced = False
                    self.post('status', '人工学习等待中：只观察已选择且处于前台的窗口；人仍在操作时绝不改变窗口焦点')
                    stop.wait(.15)
                    continue
                started = time.monotonic()
                self.control_interval = max(device.display_period, device.last_capture_ms / 1000., started - last_action_time)
                try:
                    if (device.wgc is None or device.wgc_closed) and started >= device.wgc_retry_at:
                        device.enable_wgc()
                    frame = device.image(region)
                    if not device.last_frame_valid or len(frame) != VIS_N:
                        previous = None
                        pending_click = None
                        idle_reference = None
                        stop.wait(max(.03, device.display_period))
                        continue
                    frame_stamp = device.last_capture_stamp
                    if previous is not None and frame_stamp <= last_action_time:
                        stop.wait(max(.015, device.display_period))
                        continue
                    cursor = device.cursor()
                    held = device.keys()
                    if pending_click is not None and (previous is None or
                            region != pending_click['region'] or device.capture_epoch != pending_click['epoch'] or
                            frame_stamp - pending_click['pressed_at'] > 2. or
                            math.dist(cursor, pending_click['position']) > 6.):
                        pending_click = None
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
                        old_frame, old_cursor, old_held, old_meta, old_region, old_epoch, old_crop, old_hover = previous
                        if region == old_region and device.capture_epoch == old_epoch:
                            aligned = [event for event in events if last_action_time < event[1] <= frame_stamp]
                            elapsed = max(sys.float_info.epsilon, frame_stamp - last_action_time)
                            samples = demonstration_from_events(old_cursor, cursor, old_held, held, aligned, region, elapsed)
                            if samples:
                                isolated = (len(samples) == 1 and len(aligned) == 1 and
                                            frame_stamp > aligned[0][1] and not samples[0][3])
                                click_index = completed_click_index(samples, old_held, held)
                                primary_index = 0 if isolated else click_index
                                reward = 0.
                                change = 0.
                                advanced = False
                                if primary_index is not None:
                                    action, control, distance, transitions, scroll, duration, position, down = samples[primary_index]
                                    total_motion = sum(part[2] for part in samples)
                                    group_switches = ('l+', 'l-') if click_index is not None else transitions
                                    outcome = {'action': action, 'ctrl': control, 'changed': bool(total_motion or group_switches or scroll),
                                               'moved': total_motion, 'efficacy': 1., 'switches': group_switches, 'blocked': False,
                                               'pending_scroll': False, 'scroll': scroll,
                                               'local_aligned': old_crop is not None and old_crop == device.last_crop_region and cursor == old_cursor}
                                    reward, change, advanced = observation_feedback.assess(old_frame, frame, idle_reference, outcome, cursor, region)
                                    reward = max(-1., min(1., reward))
                                    if demonstration_atlas is not None:
                                        demonstration_atlas.observe(old_frame, action, frame, reward, 1., advanced, True)
                                if click_index is not None and old_hover is not None and demonstration_atlas is not None:
                                    press_event = next((event for event in aligned if event[2] == 'l+'), None)
                                    click_position = samples[click_index][6]
                                    if (press_event is not None and old_hover[0] == demonstration_signature(old_frame) and
                                            old_hover[2] <= press_event[1] <= old_hover[2] + 2.):
                                        demonstration_atlas.remember_element(old_frame, old_hover[1], click_position, region)
                                sample_time = last_action_time
                                previous_cursor = old_cursor
                                meta_before = old_meta
                                for index, (action, control, distance, transitions, scroll, duration, position, down) in enumerate(samples):
                                    sample_time = min(frame_stamp, sample_time + duration)
                                    attributed = index == primary_index
                                    dt_sample = elapsed if attributed else duration
                                    if attributed:
                                        new_meta = self.create_meta(frame_stamp, region, cursor, old_cursor, held, scroll, elapsed, change, device.last_crop_region)
                                    else:
                                        new_meta = self.create_meta(sample_time, region, position, previous_cursor, down, scroll, duration, 0., old_crop)
                                    self.brain.learn(old_frame, meta_before, action, frame if attributed else old_frame,
                                                     new_meta, reward if attributed else 0., True, dt_sample,
                                                     control, control, action, 1., False, True,
                                                     CAPTURE_SOURCES.get(device.last_frame_backend, 0) |
                                                     (CAPTURE_VERIFIED if attributed and device.last_frame_confirmed else 0))
                                    self.control_history.append((control[0] * control[2], control[1] * control[2], control[6], reward if attributed else 0.))
                                    self.observed_count += 1
                                    meta_before = new_meta
                                    previous_cursor = position
                                if self.observed_count % max(2, math.isqrt(max(1, self.observed_count))) < len(samples):
                                    reliable = ('已采集完整点击前后截图' if click_index is not None else
                                                '已采集单动作前后截图' if isolated else '连续动作仅模仿学习，未虚构动作结果')
                                    self.post('stats', f'人工示范 {self.observed_count} 条 · 短期经验 {len(self.brain.memory)} · 自主操作 {self.iterations} 次 · {reliable}')
                                    self.post('control', f'正在学习人工鼠标示范：分解 {len(samples)} 步 · 鼠标键变化 {sum(bool(part[3]) for part in samples)} · 滚轮 {sum(part[4] for part in samples):+d}')
                                    perf = self.brain.latest_perf if isinstance(self.brain, RemoteBrain) else {}
                                    if perf and self.brain.engine_backend == 'cuda':
                                        cuda_status = ('CUDA真实训练正在运行' if perf.get('cuda_optimizer_steps', 0) else
                                                       'CUDA优化器更新已验证，等待交互样本' if perf.get('cuda_training_path_verified') else
                                                       'CUDA模型计算已验证，等待训练')
                                        self.post('gpu_state', self.brain.label + ' · ' + cuda_status + f' · 累计训练 {perf.get("training_examples", 0)} 样本')
                                switches = [switch for sample in samples for switch in sample[3]]
                                if pending_click is not None:
                                    if completed_deferred_click(pending_click, samples, held, cursor, region, device.capture_epoch, frame_stamp):
                                        original = pending_click
                                        press_action, press_control = original['press'][:2]
                                        duration = max(sys.float_info.epsilon, frame_stamp - original['frame_at'])
                                        result = {'action': press_action, 'ctrl': press_control, 'changed': True,
                                                  'moved': math.dist(original['cursor'], cursor), 'efficacy': 1.,
                                                  'switches': ('l+', 'l-'), 'blocked': False, 'pending_scroll': False,
                                                  'scroll': 0, 'local_aligned': (original['crop'] is not None and
                                                                               original['crop'] == device.last_crop_region and
                                                                               original['cursor'] == cursor)}
                                        click_reward, click_change, click_progress = observation_feedback.assess(
                                            original['frame'], frame, original['baseline'], result, cursor, region)
                                        click_reward = max(-1., min(1., click_reward))
                                        nmeta = self.create_meta(frame_stamp, region, cursor, original['cursor'], held, 0, duration, click_change, device.last_crop_region)
                                        self.brain.learn(original['frame'], original['meta'], press_action, frame, nmeta,
                                                         click_reward, True, duration, press_control, press_control,
                                                         press_action, 1., False, True,
                                                         CAPTURE_SOURCES.get(device.last_frame_backend, 0) |
                                                         (CAPTURE_VERIFIED if device.last_frame_confirmed else 0))
                                        self.control_history.append((0., 0., 0., click_reward))
                                        self.observed_count += 1
                                        if demonstration_atlas is not None:
                                            demonstration_atlas.observe(original['frame'], press_action, frame,
                                                                        click_reward, 1., click_progress, True)
                                            hover_info = original['hover']
                                            if (hover_info is not None and hover_info[0] == demonstration_signature(original['frame']) and
                                                    hover_info[2] <= original['pressed_at'] <= hover_info[2] + 2.):
                                                demonstration_atlas.remember_element(original['frame'], hover_info[1], original['position'], region)
                                    if switches or any(sample[4] for sample in samples):
                                        pending_click = None
                                if pending_click is None and click_index is None and old_held.get('l') is False and held.get('l') is True and switches == ['l+'] and not any(sample[4] for sample in samples):
                                    press_sample = next((sample for sample in samples if sample[3] == ('l+',)), None)
                                    press_event = next((event for event in aligned if event[2] == 'l+'), None)
                                    if (press_sample is not None and press_event is not None and
                                            math.dist(press_sample[6], cursor) <= 6.):
                                        pending_click = {'frame': old_frame, 'meta': old_meta, 'cursor': old_cursor,
                                                         'baseline': idle_reference, 'crop': old_crop, 'hover': old_hover,
                                                         'position': press_sample[6],
                                                         'press': press_sample, 'pressed_at': press_event[1],
                                                         'frame_at': last_action_time, 'region': region,
                                                         'epoch': device.capture_epoch}
                    old_pos = previous[1] if previous is not None and previous[4] == region else cursor
                    old_dt = max(sys.float_info.epsilon, frame_stamp - last_action_time)
                    meta = self.create_meta(frame_stamp, region, cursor, old_pos, held, 0, old_dt, 0., device.last_crop_region)
                    hover = None
                    if device.com_initialized and not any(held.values()) and device.pointer_on_target(*cursor):
                        previous_hover = previous[7] if previous is not None and previous[1] == cursor and previous[4] == region else None
                        if previous_hover is not None and previous_hover[0] == demonstration_signature(frame):
                            hover = (previous_hover[0], previous_hover[1], frame_stamp)
                        else:
                            try:
                                info = accessible_element_at(cursor)
                                if safe_demonstrated_element(info, cursor, allow_unknown=True):
                                    hover = (demonstration_signature(frame), info, frame_stamp)
                            except (OSError, ValueError, RuntimeError, ctypes.ArgumentError):
                                pass
                    if (not events and previous is not None and previous[4] == region and
                            previous[5] == device.capture_epoch and not any(held.values()) and
                            not any(previous[2].values())):
                        idle_reference = previous[0]
                    else:
                        idle_reference = None
                    previous = (frame, cursor, held, meta, region, device.capture_epoch, device.last_crop_region, hover)
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
                    idle_reference = None
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
        launchable = (available and self.folder_selected and not self.manual_start_pending and
                      self.listing.get(self.combo_var.get()) is not None and not self.exit_stop.is_set())
        self.start_button.configure(state='normal' if launchable else 'disabled')

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
        if kind in ('control', 'stats', 'capture', 'accelerator', 'status', 'goal', 'preview', 'fps', 'gpu_state', 'storage', 'consolidation', 'checkpoint', 'metrics'):
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
                folder = Path(val)
                self.folder_selected = True
                persist_data_folder(folder)
                self.folder = folder
                self.data_folder = folder
                self.folder_text.set(str(folder))
                self.storage_checked_at = 0.
                self.backend.set('未启动')
                self.issue.set('无')
                self.task_failed = False
                self.phase.set('空闲')
                self.status.set('已切换数据目录，旧目录数据独立保留；现在可以选择目标窗口')
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
                    if val == 'control':
                        self.transition_control('空闲')
                    if self.pending_folder is not None:
                        self.root.after_idle(self.apply_pending_folder)
                    elif val == 'observe' and self.manual_start_pending and not self.keyboard_stopped_control.is_set():
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
            stats = str(updates['stats']).split(' · ')
            self.statistics.set(' · '.join(stats[:4]))
            self.learning_summary.set('学习：' + ' · '.join(stats[:4]))
            self.stat_pages = tuple(' · '.join(stats[i:i + 4]) for i in range(0, len(stats), 4))
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
        if 'consolidation' in updates:
            self.consolidation_status.set(updates['consolidation'])
        if 'checkpoint' in updates:
            self.checkpoint_status.set(updates['checkpoint'])
        if 'metrics' in updates or 'stats' in updates:
            self.metric_pages = tuple(updates.get('metrics', getattr(self, '_main_metric_pages', ()))) + self.stat_pages
            if 'metrics' in updates:
                self._main_metric_pages = tuple(updates['metrics'])
            self.metric_page %= max(1, len(self.metric_pages))
        if self.metric_pages:
            if time.monotonic() >= self.metric_rotate_at:
                self.metric_page = (self.metric_page + 1) % len(self.metric_pages)
                self.metric_rotate_at = time.monotonic() + 6.
            self.metric_text.set(f'监控 {self.metric_page + 1}/{len(self.metric_pages)} · ' + self.metric_pages[self.metric_page])
        if 'accelerator' in updates and self.brain is not None and not self.brain.accelerated and self.mode != 'closed':
            self.backend.set(self.brain.label + ' · ' + str(updates['accelerator'])[:105])
        if 'preview' in updates:
            self.render_preview(updates['preview'])
        if 'control' in updates:
            latest_control = updates['control']
        if latest_control is not None:
            self.control_details.set(latest_control)
        if os.name == 'nt':
            healthy = self.keyboard_healthy()
            self.safety_text.set(('鼠标' + self.control_state + ' · ' if self.mode == 'control' else '') + ('键盘急停在线 · AI注入事件独立识别 · 用户输入优先' if healthy else '输入监控恢复中 · 禁止自主动作'))
            if self.mode == 'control' and not healthy:
                self.status.set('键盘监控正在恢复；暂停鼠标操作')
        if self.start_queued is not None:
            selection = self.start_queued
            if not self.manual_start_pending or self.keyboard_stopped_control.is_set() or self.mode != 'idle' or selection != self.combo_var.get():
                self.start_queued = None
            elif self.keyboard_healthy():
                self.start_queued = None
                self.root.after_idle(self.start)
        if not self.exit_stop.is_set():
            self.update_hud()
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
                raw = f'P6\n{VIS_W} {VIS_H}\n255\n'.encode('ascii') + bytes(interleaved)
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
        photo = tk.PhotoImage(data=f'P6\n{VIS_W} {VIS_H}\n255\n'.encode('ascii') + bytes(data), format='PPM')
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
            self.status.set('AI 正在自主操作，按任意键盘按键停止控制后再选择数据目录')
            return
        new = filedialog.askdirectory(parent=self.root, initialdir=str(self.folder), title='选择 AI 数据存放文件夹')
        if not new:
            return
        folder = Path(new)
        if folder == self.folder:
            self.folder_selected = True
            persist_data_folder(folder)
            self.folder_text.set(str(folder))
            self.preload_selected()
            return
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
            self.folder_selected = True
            persist_data_folder(folder)
            self.preload_selected()
            return
        if any(worker is not None and worker.is_alive() for worker in (self.worker, self.online_worker)):
            self.status.set('控制线程仍在退出，请稍后更换目录')
            return
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
                self.consolidated_steps.clear()
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
                            samples = [(row[0], row[1], values) for row in selected if (values := self.brain.scores(row[0], row[1])) is not None]
                        if samples and not cancel.is_set():
                            self.post('accelerator', 'GPU 正在学习轻量模型已经掌握的操作偏好')
                            try:
                                migrated = ready.distill_policy(samples, cancel)
                                if migrated < len(samples) and not cancel.is_set():
                                    raise RuntimeError('未完成全部策略迁移样本')
                                self.post('accelerator', f'GPU 已训练迁移 {migrated} 条策略样本')
                            except Exception as migration_error:
                                if not cancel.is_set():
                                    if ready.engine_backend == 'cuda':
                                        self.post('accelerator', '轻量策略迁移未完成，CUDA 已通过独立训练验证，将继续基于交互经验训练：' + str(migration_error)[:65])
                                    else:
                                        raise RuntimeError('策略迁移失败，暂时保留基础引擎') from migration_error
                    available = sum(not row[12] for row in rows)
                    if available >= 2 and isinstance(self.brain, LiteBrain) and not cancel.is_set():
                        iterations = max(1, min(int(math.sqrt(available)), (os.cpu_count() or 1) * 2))
                        self.post('accelerator', f'深度学习引擎正在后台预训练交互经验（{iterations} 批）')
                        try:
                            trained = ready.warm_train(iterations, cancel)
                            self.post('accelerator', f'深度学习引擎已完成 {trained} 批训练，准备接管推理')
                        except Exception as warm_error:
                            self.post('accelerator', 'GPU 预训练验证失败：' + str(warm_error)[:75])
                            raise RuntimeError('GPU 训练路径未通过预训练验证') from warm_error
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
                        retry = min(180., max(12., elapsed * (2 ** min(self.acceleration_failures, 5))))
                        self.next_backend_retry = time.monotonic() + retry
                    elif valid:
                        self.acceleration_failures = 0
                        self.next_backend_retry = 0.
                if ready is not None:
                    ready.close()

        self.acceleration_thread = threading.Thread(target=prepare, daemon=True)
        self.acceleration_thread.start()

    def retire_backend(self, backend):
        def release():
            try:
                backend.close()
            except Exception as error:
                self.post('status', '旧计算后端释放异常：' + str(error)[:75])
            finally:
                with self.retired_lock:
                    self.retired_workers.discard(threading.current_thread())
        worker = threading.Thread(target=release, daemon=True)
        with self.retired_lock:
            self.retired_workers.add(worker)
        worker.start()

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
            with candidate.save_lock:
                new_rows = list(candidate.memory)
                new_count = len(new_rows)
                new_steps = candidate.steps
                new_last = new_rows[-1] if new_rows else None
            same_rows = new_count == len(old_rows) and experience_digest(old_rows) == experience_digest(new_rows)
            if not same_rows or old_steps > new_steps:
                difference = old_steps - new_steps
                boundary_matches = (difference == len(old_rows) and new_count == 0) or (0 < difference < len(old_rows) and new_last == old_rows[-difference - 1])
                if difference > 0 and boundary_matches:
                    candidate.append_records(old_rows[-difference:], old_steps)
                else:
                    candidate.sync_fast(old_rows, max(old_steps, new_steps))
            if isinstance(previous, RemoteBrain) and isinstance(candidate, RemoteBrain):
                self.post('accelerator', '正在迁移完整网络权重、目标模型和优化器状态')
                try:
                    migrated = previous.transfer_policy_to(candidate)
                    optimizer_state = '完整优化器状态' if migrated.get('optimizer_restored', True) else '已重建优化器状态'
                    self.post('accelerator', f'已迁移 {migrated["parameters"]:,} 个模型参数 · {optimizer_state}')
                except (OSError, RuntimeError, ValueError, KeyError) as migration_error:
                    raise RuntimeError('网络权重迁移失败，继续使用原后端：' + str(migration_error)[:90]) from migration_error
            if old_rows and isinstance(previous, LiteBrain):
                evaluated = [row for row in old_rows if row[2] != IDLE_ACTION and
                             (row[5] != 0. or (len(row) > 13 and row[13]))]
                if len(evaluated) >= 16:
                    sample = random.sample(evaluated, min(48, len(evaluated)))
                    prior_quality = previous.policy_metric(sample)
                    candidate_quality = candidate.policy_metric(sample)
                    if prior_quality is not None and candidate_quality is not None:
                        if policy_regressed(prior_quality, candidate_quality, sample):
                            if candidate.engine_backend != 'cuda':
                                raise RuntimeError(f'新后端策略质量下降 {prior_quality:.1%}→{candidate_quality:.1%}，保留原模型')
                            self.post('accelerator', f'CUDA 训练已验证，策略抽样 {prior_quality:.1%}→{candidate_quality:.1%}，已同步经验并继续在线训练')
                        else:
                            self.post('accelerator', f'后端策略抽样对照 {prior_quality:.1%}→{candidate_quality:.1%}，未检测到显著退化')
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
            self.retire_backend(previous)
            self.post('status', '已切换到 ' + candidate.label + '，交互经验已同步，旧资源正在后台释放')
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
        if not self.folder_selected:
            return
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
                    candidate = RemoteBrain(self.data_folder, runtime, backend, recovery_cancel, cache_folder=runtime_folder)
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
        self.manual_start_pending = False
        self.control_lease_active = False
        self.takeover_permission.clear()
        self.explore_permission.clear()
        self.handoff_pending = False
        self.start_queued = None
        self.user_override.set()
        self.control_stop.set()
        self.release_signal.set()
        self.transition_control('已停止')
        self.mouse_monitor_armed.clear()
        self.control_heartbeat = 0.
        self.online_stop.set()
        if not fast and isinstance(self.brain, RemoteBrain):
            self.brain.cancel_train()
        active = self.active_io
        if active is not None and (self.release_worker is None or not self.release_worker.is_alive()):
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

    def consolidate_learning(self, brain):
        if self.mode != 'observe' or self.backend_recovering.is_set() or self.online_stop.is_set():
            return False
        key = (str(self.data_folder), type(brain).__name__, getattr(brain, 'engine_backend', 'lite'))
        with brain.save_lock:
            steps = brain.steps
            records = list(brain.memory)
        threshold = max(16, math.isqrt(max(1, len(records))) * 2)
        if len(records) < 32 or steps - self.consolidated_steps.get(key, 0) < threshold:
            return False
        self.consolidated_steps[key] = steps
        split = sleep_split(records)
        if split is None:
            return False
        training_scenes = {session_signature(item[0]) for item in split[0]}
        validation_scenes = {session_signature(item[0]) for item in split[1]}
        unseen_coverage = len(validation_scenes - training_scenes) / max(1, len(validation_scenes))
        stop = AnyStop(self.online_stop, self.exit_stop, self.control_stop)
        started = False
        try:
            self.post('consolidation', '自动巩固：使用独立验证集与审计集检查新模型')
            brain.begin_sleep()
            started = True
            batches = max(2, min(8, int(math.log2(2. + len(records)))))
            completed = 0
            for step in range(batches):
                if stop.is_set() or self.mode != 'observe' or self.brain is not brain:
                    brain.abort_sleep()
                    started = False
                    self.post('consolidation', '自动巩固：被实时任务抢占，已恢复原模型')
                    return False
                trained = brain.train(1, stop)
                if not trained:
                    break
                completed += trained
                if step % 2 or step == batches - 1:
                    brain.sleep_progress()
            if stop.is_set() or self.mode != 'observe' or self.brain is not brain:
                brain.abort_sleep()
                started = False
                return False
            result = brain.end_sleep()
            started = False
            accepted = bool(result is not None and result[0] is True)
            if accepted:
                self.post('consolidation', f'巩固保留：验证误差 {result[1]:.4f}→{result[2]:.4f}，新场景验证覆盖 {unseen_coverage:.0%}，审计通过')
                self.schedule_checkpoint()
            else:
                self.post('consolidation', f'巩固回滚：{completed} 批未达到改进标准 · 新场景验证覆盖 {unseen_coverage:.0%} · 原策略保留')
            return True
        except Exception:
            if started:
                try:
                    brain.abort_sleep()
                except Exception:
                    pass
            raise

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
                if isinstance(brain, RemoteBrain):
                    brain.interactive = self.mode == 'control' and self.mouse_monitor_armed.is_set()
                with brain.save_lock:
                    train_count = sum(not row[12] for row in brain.memory)
                if train_count >= 2:
                    if self.mode == 'observe' and not self.online_stop.is_set() and self.consolidate_learning(brain):
                        pass
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
                rebalance_replay_memory(brain, pressure)
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
            self.brain.reset_train_preempt()
        self.online_worker = threading.Thread(target=self.online_job, args=(self.brain,), daemon=True)
        self.online_worker.start()

    def request_start(self):
        if self.exit_stop.is_set() or self.switching_folder or not self.folder_selected:
            self.status.set('请先选择数据文件夹')
            return
        if os.name != 'nt' or struct.calcsize('P') != 8:
            self.status.set('需要 Windows 11 x64 与 64 位 Python 运行环境')
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None:
            self.status.set('请先选择有效目标窗口')
            return
        if self.mode not in ('idle', 'observe'):
            return
        self.keyboard_stopped_control.clear()
        self.control_stop.clear()
        self.manual_start_pending = True
        self.control_lease_active = False
        self.takeover_window = hwnd
        self.takeover_permission.set()
        self.explore_permission.set()
        self.handoff_pending = self.mode == 'observe'
        self.task_failed = False
        self.task_outcome = None
        self.status.set('已收到绿色按钮启动指令，正在将控制权交给所选窗口；任意键盘输入立即取消')
        self.phase.set('启动 AI 控制')
        if isinstance(self.brain, RemoteBrain):
            self.brain.preempt_training()
        self.online_stop.set()
        if self.mode == 'idle':
            self.session_hwnd = hwnd
        else:
            self.observer_stop.set()
        self.activate_selected_window(hwnd)
        if self.mode == 'idle':
            self.root.after(180, self.start)
        self.update_buttons()

    def start(self):
        if not self.manual_start_pending or self.keyboard_stopped_control.is_set() or self.exit_stop.is_set():
            return
        if not self.folder_selected or os.name != 'nt' or struct.calcsize('P') != 8:
            self.revoke_takeover_permission()
            self.status.set('请使用 Windows 11 x64 和 64 位 Python，并选择数据文件夹')
            return
        if not self.keyboard_healthy():
            self.start_queued = self.combo_var.get()
            self.status.set('等待键盘急停监控完成初始化')
            return
        if self.mode != 'idle' or (self.worker is not None and self.worker.is_alive()):
            self.root.after(150, self.start)
            return
        hwnd = self.listing.get(self.combo_var.get())
        if hwnd is None or hwnd != self.takeover_window or not u.IsWindow(hwnd):
            self.revoke_takeover_permission()
            self.status.set('目标窗口已经关闭或变化，请重新选择窗口')
            return
        self.session_hwnd = hwnd
        if not self.takeover_allowed():
            if associated_foreground_window(hwnd) is None and self.human_idle():
                self.activate_selected_window(hwnd)
            self.status.set('正在等待目标窗口成为前台、键盘监控就绪及人工输入结束；本次启动请求保持有效，按任意键取消')
            self.root.after(150, self.start)
            return
        if self.online_worker is not None and self.online_worker.is_alive():
            if isinstance(self.brain, RemoteBrain):
                self.brain.preempt_training()
            self.status.set('正在移交后台训练线程，随后开始控制')
            self.root.after(90, self.start)
            return
        self.data_folder, self.environment_code = environment_for(self.folder, hwnd, self.combo_var.get())
        try:
            if not u.IsWindow(hwnd):
                raise RuntimeError('所选窗口已经关闭，请刷新窗口列表')
            if associated_foreground_window(hwnd) is None:
                self.root.after(150, self.start)
                return
            rect = RECT()
            point = POINT(0, 0)
            if not u.GetClientRect(hwnd, ctypes.byref(rect)) or not u.ClientToScreen(hwnd, ctypes.byref(point)):
                raise RuntimeError('无法获取目标窗口客户区')
            width, height = rect.right - rect.left, rect.bottom - rect.top
            if width < 8 or height < 8:
                raise RuntimeError('目标窗口客户区没有足够的安全光标范围')
            if not self.takeover_allowed():
                self.root.after(150, self.start)
                return
            point_cursor = POINT()
            if not u.GetCursorPos(ctypes.byref(point_cursor)):
                raise RuntimeError('无法读取鼠标位置')
        except Exception as error:
            self.revoke_takeover_permission()
            self.phase.set('无法启动')
            self.issue.set(str(error))
            self.status.set('鼠标无法进入所选窗口：' + str(error))
            return
        self.phase.set('窗口已激活 · 准备模型')
        self.fps_text.set('控制 FPS：正在采样')
        self.set_progress(0, '启动目标窗口')
        self.task_failed = False
        self.task_outcome = None
        self.issue.set('无')
        self.status.set('目标窗口准备接管；真实鼠标输入优先，任意键盘按键立即停止')
        self.control_details.set('正在等待模型就绪 · 鼠标尚未接管')
        self.backend_recovering.clear()
        self.mouse_monitor_armed.clear()
        self.mode = 'control'
        self.transition_control('准备中')
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
        self.transition_control('安全暂停')
        self.control_heartbeat = 0.
        self.user_override.set()
        if device is not None:
            device.interrupt_release()
        self.post('status', '安全暂停：' + reason + '；按任意键停止，用户空闲且条件恢复后继续')

    def safety_sentinel(self):
        canceled = False
        while not self.exit_stop.is_set():
            self.safety_alive_at = time.monotonic()
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
                elif not self.keyboard_healthy():
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
                elif (not self.backend_recovering.is_set() and self.mouse_monitor_armed.is_set() and
                      self.control_heartbeat > 0 and
                      ((self.inference_deadline > 0 and time.monotonic() > self.inference_deadline) or
                       (self.inference_deadline <= 0 and time.monotonic() - self.control_heartbeat > max(3., self.watchdog_limit)))):
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
        self.safety_alive_at = 0.
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
            if self.keyboard_sentinel():
                failures = 0
                continue
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
                    self.keyboard_event_signal.set()
                    self.user_override.set()
                    if self.mode == 'control' or self.manual_start_pending:
                        self.control_stop.set()
                        self.keyboard_stopped_control.set()
                        self.mouse_monitor_armed.clear()
                        self.release_signal.set()
                return u.CallNextHookEx(None, code, wparam, lparam)
            def scrolled(code, wparam, lparam):
                if code >= 0:
                    try:
                        event = ctypes.cast(lparam, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                        kind = int(wparam)
                        injected_by_ai = own_mouse_event(event.flags, event.extra)
                        if injected_by_ai:
                            with self.hook_event_lock:
                                self.ai_mouse_attribution[kind] += 1
                            if kind == 0x20A:
                                delta = ctypes.c_short((event.mouseData >> 16) & 0xffff).value
                                with self.wheel_lock:
                                    self.wheel_events.append(delta)
                        else:
                            key = {0x201: 'l+', 0x202: 'l-', 0x204: 'r+', 0x205: 'r-', 0x207: 'm+', 0x208: 'm-'}.get(kind, '')
                            delta = ctypes.c_short((event.mouseData >> 16) & 0xffff).value if kind == 0x20A else 0
                            self.user_override.set()
                            self.release_signal.set()
                            with self.hook_event_lock:
                                self.hook_mouse_events.append((time.monotonic(), (key, int(event.pt.x), int(event.pt.y), delta)))
                    except Exception:
                        self.user_override.set()
                        self.release_signal.set()
                        with self.hook_event_lock:
                            self.hook_mouse_events.append((time.monotonic(), None))
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
                if self.keyboard_event_signal.is_set():
                    self.keyboard_event_signal.clear()
                    self.human_input(keyboard=True)
                    if self.mode == 'control':
                        self.emergency_stop('检测到真实键盘输入，已停止鼠标控制', fast=True)
                with self.hook_event_lock:
                    events = tuple(self.hook_mouse_events)
                    self.hook_mouse_events.clear()
                for stamp, event in events:
                    self.human_input(event, stamp=stamp)
                self.exit_stop.wait(.012)
        except Exception as ex:
            self.post('status', '键盘安全监控异常：' + str(ex)[:85])
        finally:
            self.keyboard_ready.clear()
            self.keyboard_alive_at = 0.
            self.user_override.set()
            self.release_signal.set()
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
                        active.interrupt_release()
                    except Exception as error:
                        self.emergency_stop('键盘安全钩子失效，无法确认鼠标已释放：' + str(error)[:90])
                self.post('status', '键盘钩子已退出，鼠标控制已暂停；键盘监控恢复前不会继续操作')

    def create_meta(self, now, region, cursor, prior, held, scroll, dt, diff, crop=None):
        x, y, w, h = region
        cx, cy, cw, ch = crop if crop is not None else region
        crop_features = (max(0., min(1., (cx - x) / max(1, w))),
                         max(0., min(1., (cy - y) / max(1, h))),
                         max(0., min(1., cw / max(1, w))),
                         max(0., min(1., ch / max(1, h))))
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
                float(scroll != 0), *crop_features, *self.environment_code]

    def end_experience(self, feedback=None):
        brain = self.brain
        if brain is not None:
            try:
                brain.mark_last_done()
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
                    target = brain.checkpoint()
                    brain.await_checkpoint(target, timeout=100.)
                else:
                    brain.save()
                atlas = self.goal_atlas
                if atlas is not None:
                    atlas.save()
                self.last_checkpoint_step = snapshot_step
                self.last_checkpoint_time = time.monotonic()
                self.post('checkpoint', f'最近成功保存：第 {brain.generation} 代 · {len(brain.memory)} 条短期经验')
                elapsed = self.last_checkpoint_time - started
                self.last_checkpoint_duration = elapsed if not self.last_checkpoint_duration else .75 * self.last_checkpoint_duration + .25 * elapsed
            except Exception as ex:
                self.post('error', '定期保存失败：' + str(ex)[:110])
        self.saver = threading.Thread(target=persist, daemon=True)
        self.saver.start()

    def await_target(self, device, stop, detail):
        self.mouse_monitor_armed.clear()
        self.control_heartbeat = 0.
        self.transition_control('安全暂停')
        device.quick_release()
        self.post('phase', '等待目标窗口与有效截图')
        self.post('status', '鼠标已安全暂停；' + str(detail)[:95] + '。窗口和画面恢复后自动继续，按任意键停止')
        while not stop.is_set():
            if not self.keyboard_healthy():
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
                        self.transition_control('控制中')
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

    def resync_control_frame(self, device, region, stop, feedback, detail):
        device.quick_release()
        self.end_experience(feedback)
        current = device.region()
        if current is None or not device.foreground():
            return self.await_target(device, stop, detail)
        try:
            device.prepare_cursor(current, stop)
            frame = device.image(current)
        except InterruptedError:
            raise
        except (OSError, RuntimeError, ValueError):
            return self.await_target(device, stop, detail)
        if not device.last_frame_valid or len(frame) != VIS_N:
            return self.await_target(device, stop, detail)
        self.control_heartbeat = time.monotonic()
        self.mouse_monitor_armed.set()
        return current, frame

    def safe_action_options(self, io, region, frame, meta, held, demonstrated, exploration, planner, visual_targets=()):
        mouse = io.cursor()
        native_targets = io.semantic_targets(region, frame, visual_targets)
        permitted = matching_demonstrations(demonstrated, frame, meta)
        if planner is not None and io.com_initialized and io.pointer_on_target(*mouse):
            try:
                element = accessible_element_at(mouse)
                if planner.authorizes_element(element_scene_signature(frame), element, mouse, region):
                    permitted.add(BUTTON_ACTIONS[('l', True)])
            except (OSError, ValueError, RuntimeError, ctypes.ArgumentError):
                pass
        exploring = (exploration.allowable(frame, meta, io.explorable_controls(mouse, io.down), io.down)
                     if self.explore_permission.is_set() and self.takeover_permission.is_set() else set())
        return native_targets, permitted, set(candidates(held)), exploring

    def control_job(self, hwnd):
        io = None
        process_mutex = None
        mutex_acquired = False
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
        autonomous_left_presses = 0
        confirmed_navigation_changes = 0
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
            window_lock_name = 'Local\\WindowMouseAI_' + str(int(hwnd))
            process_mutex = kernel32.CreateMutexW(None, False, window_lock_name)
            if not process_mutex:
                raise OSError(ctypes.get_last_error(), '无法创建目标窗口的排他控制锁')
            mutex_result = kernel32.WaitForSingleObject(process_mutex, 0)
            if mutex_result not in (0, 0x80):
                raise RuntimeError('目标窗口已由另一个鼠标 AI 实例控制，禁止同时接管')
            mutex_acquired = True
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
            io.keyboard_heartbeat_guard = self.keyboard_healthy
            io.demonstrated_element_atlas = planner
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
            if not self.keyboard_healthy():
                self.post('phase', '正在恢复键盘急停监控')
                self.post('status', '键盘急停监控暂未就绪，自动等待恢复；期间绝不发送鼠标动作')
                while not stop.is_set() and not self.keyboard_healthy():
                    if io.keyboard_activity():
                        self.keyboard_stopped_control.set()
                        self.emergency_stop('检测到键盘输入，已停止鼠标控制')
                        break
                    stop.wait(.05)
                if stop.is_set():
                    raise InterruptedError('键盘已停止鼠标控制')
            self.control_heartbeat = time.monotonic()
            self.mouse_monitor_armed.set()
            self.post('progress', (100, '初始化 4/4 · 已验证首帧及控制安全条件，无人输入后开始动作'))
            self.transition_control('控制中')
            self.post('phase', 'AI 控制中')
            self.post('status', '自主探索已启动；所有按钮及滚轮动作可自主选择，任意键盘输入立即停控')
            while not stop.is_set():
                try:
                    if not self.human_idle():
                        raise InterruptedError('用户重新操作或当前控制授权已失效')
                    if not interactive_desktop():
                        raise RuntimeError('Windows 桌面已锁定或会话不再可交互')
                    if (io.wgc is None or io.wgc_closed) and (self.capture_worker is None or not self.capture_worker.is_alive()):
                        source_lost = io.wgc_closed
                        if source_lost:
                            io.quick_release()
                        wgc_restarted = io.enable_wgc()
                        if wgc_restarted:
                            self.post('capture', 'WGC 截图后端已自动启用，正在同步最新画面')
                        if source_lost or wgc_restarted:
                            io.quick_release()
                            self.end_experience(feedback)
                            prev_frame = io.image(region)
                            reference_frame = prev_frame
                            previous_epoch = io.capture_epoch
                            prev_pos = io.cursor()
                            prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                            prev_change = 0.
                            continue
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
                    if not self.keyboard_healthy():
                        raise RuntimeError('键盘监控暂时不可用')
                    if self.online_error is not None:
                        issue = self.online_error
                        self.online_error = None
                        self.recover_learning_backend(issue)
                        if stop.is_set():
                            raise InterruptedError('后端恢复期间收到急停')
                        region, prev_frame = self.resync_control_frame(io, region, stop, feedback, '学习后端已恢复，重新采集画面')
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                        prev_change = 0.
                        last_tick = time.monotonic()
                        self.start_online()
                        continue
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
                    frame_crop = io.last_crop_region
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
                    meta = self.create_meta(start, region, mouse, prev_pos, held, scroll, prev_dt, prev_change, io.last_crop_region)
                    infer_start = time.monotonic()
                    self.inference_deadline = infer_start + max(18., self.watchdog_limit * 2.)
                    visual_targets = io.visible_targets(frame)
                    if demonstrated_brain is not self.brain:
                        with self.brain.save_lock:
                            demonstrated = demonstrated_controls(self.brain.memory)
                        demonstration_targets = demonstrated_target_cells(demonstrated)
                        demonstrated_brain = self.brain
                    native_targets, permitted, allowed_actions, exploratory = self.safe_action_options(
                        io, region, frame, meta, held, demonstrated, exploration, planner, visual_targets)
                    suggested_targets = navigator.targets(native_targets + visual_targets, meta, session_signature(frame))
                    advice = planner.plan(frame, allowed_actions) if planner is not None else None
                    try:
                        action, ctrl = self.brain.choose(frame, meta, io.down, suggested_targets, allowed_actions)
                    except Exception as ex:
                        self.inference_deadline = 0.
                        self.recover_learning_backend(ex)
                        if stop.is_set():
                            raise InterruptedError('后端恢复期间收到急停')
                        region, prev_frame = self.resync_control_frame(io, region, stop, feedback, '计算后端已恢复，重新采集画面')
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                        prev_change = 0.
                        last_tick = time.monotonic()
                        self.start_online()
                        continue
                    finally:
                        self.inference_deadline = 0.
                    if advice is not None and advice[0] in allowed_actions and random.random() < advice[1] and advice[2] > 0.:
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
                    self.watchdog_limit = max(3., measured_inference + measured_capture + observed_cycle + io.display_period)
                    self.control_heartbeat = time.monotonic()
                    if stop.is_set():
                        raise InterruptedError('控制已停止')
                    if len(history) >= 4 and infer_ms > max(io.display_period * 1000., capture_ms) and infer_ms > history[(3 * (len(history) - 1)) // 4] + 1.5 * (history[(3 * (len(history) - 1)) // 4] - history[(len(history) - 1) // 4]):
                        self.post('status', '模型推理延迟过高，已丢弃过期动作并重新采集窗口')
                        region, prev_frame = self.resync_control_frame(io, region, stop, feedback, '推理延迟过高，重新获取当前画面')
                        reference_frame = prev_frame
                        previous_epoch = io.capture_epoch
                        prev_pos = io.cursor()
                        prev_dt = max(sys.float_info.epsilon, io.last_capture_ms / 1000., io.display_period)
                        prev_change = 0.
                        last_tick = time.monotonic()
                        continue
                    if ctrl is None:
                        ctrl = anchor_control(action)
                    if action not in allowed_actions:
                        raise RuntimeError('模型输出的按钮状态与当前鼠标状态冲突')
                    progress_probability = (feedback.progress_effects + .5) / (feedback.total + 1.)
                    unexpected_stagnation = math.exp(feedback.stagnant * math.log1p(-progress_probability)) < 1. / (1. + feedback.total)
                    if feedback.loop_count and unexpected_stagnation:
                        action = explore_action(tuple(allowed_actions), meta, self.brain.steps, frame, suggested_targets)
                        ctrl = exploratory_control(action, meta)
                    if not isinstance(self.brain, RemoteBrain) or getattr(self.brain, 'steps', 0) < max(1, REPLAY_LIMIT // 2):
                        guided_action, guided_ctrl = navigator.guide(action, ctrl, meta, io.down, self.brain.steps)
                        if guided_action in allowed_actions:
                            action, ctrl = guided_action, guided_ctrl
                    if len(ctrl) != CTRL_N or not all(math.isfinite(v) for v in ctrl):
                        raise RuntimeError('模型动作参数异常')
                    if exploration.pending_release:
                        if io.down.get('l', False):
                            action = BUTTON_ACTIONS[('l', False)]
                            ctrl = anchor_control(action)
                        exploration.pending_release = False
                    elif exploratory and not permitted and not any(io.down.values()):
                        action, ctrl = exploration.choose(action, ctrl, exploratory, feedback)
                    if action not in allowed_actions:
                        action = explore_action(tuple(allowed_actions), meta, self.brain.steps, frame, suggested_targets)
                        ctrl = anchor_control(action)
                    stale_button = io.stale_button()
                    if stale_button is not None:
                        action = BUTTON_ACTIONS[(stale_button, False)]
                        ctrl = anchor_control(action)
                        exploration.pending_release = False
                    action, ctrl = permitted_autonomous_control(action, ctrl)
                    if action == BUTTON_ACTIONS[('l', True)] and action in exploratory and action not in permitted:
                        exploration.pending_release = True
                    if not self.takeover_allowed():
                        raise InterruptedError('当前控制授权已失效')
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
                        outcome['visual_target_progress'] = visual_target_pointer_gain(navigator.focus, mouse, new_mouse, region, meta)
                    capture_code = CAPTURE_SOURCES.get(io.last_frame_backend, 0) | (CAPTURE_VERIFIED if io.last_frame_confirmed else 0)
                    outcome['capture_confidence'] = (1. if io.last_frame_confirmed else
                                                     .85 if io.last_frame_backend == 'gdi' else .7)
                    outcome['local_aligned'] = (frame_crop is not None and frame_crop == io.last_crop_region and
                                                mouse == new_mouse and outcome.get('moved', 0.) < 1.)
                    reward, change, advanced = feedback.assess(frame, nxt, reference_frame, outcome, new_mouse, region)
                    if action == BUTTON_ACTIONS[('l', True)] and 'l+' in outcome['switches']:
                        autonomous_left_presses += 1
                        if io.last_frame_confirmed and session_signature(frame) != session_signature(nxt):
                            confirmed_navigation_changes += 1
                    exploration.observe(action, frame, nxt, outcome)
                    navigator.observe(reward, outcome)
                    if planner is not None:
                        planner.observe(frame, action, nxt, reward, outcome['efficacy'], advanced)
                    self.audit_sum += reward
                    self.audit_samples += 1
                    actual_dt = max(time.get_clock_info('monotonic').resolution, io.last_capture_stamp - frame_stamp)
                    new_scroll = self.wheel_delta() if self.wheel_hook_ready else outcome['scroll']
                    next_held = io.keys()
                    nmeta = self.create_meta(time.monotonic(), region, new_mouse, mouse, next_held, new_scroll, actual_dt, change, io.last_crop_region)
                    try:
                        _, _, next_allowed, _ = self.safe_action_options(
                            io, region, nxt, nmeta, next_held, demonstrated, exploration, planner)
                    except (OSError, ValueError, RuntimeError, ctypes.ArgumentError):
                        next_allowed = set(future_action_candidates(nmeta, SAFE_FUTURE_MASK))
                    stage_times['反馈'].append((time.monotonic() - feedback_start) * 1000.)
                    if holdout_remaining <= 0:
                        holdout_mode = not holdout_mode
                        records_seen = max(1, len(self.brain.memory))
                        correlation_length = max(2, math.isqrt(records_seen))
                        holdout_remaining = correlation_length if holdout_mode else max(correlation_length, math.ceil(records_seen ** .75))
                    holdout_remaining -= 1
                    learn_start = time.monotonic()
                    try:
                        self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'], ctrl, outcome['action'], outcome['efficacy'], holdout_mode, False, capture_code, allowed_actions, next_allowed)
                    except Exception as error:
                        self.recover_learning_backend(error)
                        if stop.is_set():
                            raise InterruptedError('后端恢复期间收到急停')
                        io.prepare_cursor(region, stop)
                        self.control_heartbeat = time.monotonic()
                        self.mouse_monitor_armed.set()
                        self.brain.learn(frame, meta, action, nxt, nmeta, reward, False, actual_dt, outcome['ctrl'], ctrl, outcome['action'], outcome['efficacy'], holdout_mode, False, capture_code, allowed_actions, next_allowed)
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
                            cuda_status = ('CUDA真实训练正在运行' if perf.get('cuda_optimizer_steps', 0) else
                                           'CUDA优化器更新已验证，等待交互样本' if perf.get('cuda_training_path_verified') else
                                           'CUDA模型计算已验证，等待训练')
                            self.post('gpu_state', self.brain.label + ' · ' + cuda_status + f' · 累计训练 {perf.get("training_examples", 0)} 样本')
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
                        archival_health = (f' · 归档排队 {archive.pending.qsize()} · 溢出未归档 {archive.dropped} · 失败尝试 {archive.failed_writes} · 自动恢复 {archive.recovered_writes} · 写盘P95 {p95(archive.write_ms):.1f}ms · 排队P95 {p95(archive.queue_ms):.1f}ms' + (' · 归档异常 ' + archive.error[:65] if archive.error else '')) if archive is not None else ''
                        with self.hook_event_lock:
                            attributed_events = sum(self.ai_mouse_attribution.values())
                        self.post('metrics', (
                            f'动作质量：执行率 {feedback.efficacy_total / max(1, feedback.total):.1%} · 受阻率 {feedback.blocks / max(1, feedback.total):.1%} · 重复率 {feedback.repeats / max(1, feedback.total):.1%} · AI归属鼠标事件 {attributed_events}',
                            f'探索实绩：左键按下 {autonomous_left_presses} · 按下后确认画面变化 {confirmed_navigation_changes} · 可用动作 {ACT_N} 种 · 已见场景 {len(feedback.frequency)}',
                            f'学习证据：可控进展 {feedback.progress_effects} · 视觉目标接近 {feedback.visual_target_advances} · 示范目标确认 {feedback.verified_goal_matches} · 因果观测 {feedback.causal_evidence} · 实际任务成功率需要任务定义',
                            f'运行性能：{fps:.1f}FPS · 采集 {io.last_capture_ms:.0f}ms · 推理P95 {p95(infer_times):.0f}ms · 保存代 {self.brain.generation}',
                        ))
                        self.post('stats', f'短期经验 {len(self.brain.memory)} · 长期经验 {archived} · 实时经验上限 {getattr(self.brain, "replay_runtime_limit", REPLAY_LIMIT)} · 操作 {self.iterations} · 可控进展 {feedback.progress_effects}/{feedback.total} · 示范目标画面匹配 {feedback.demonstrated_goal_matches} · 连续画面确认 {feedback.verified_goal_matches} · 示范指针接近 {feedback.demonstrated_pointer_advances} · 视觉目标接近 {feedback.visual_target_advances} · 试探点击 {exploration.attempts} 次 / 可观测画面变化 {exploration.effects} 次 · 重复可归因 {feedback.causal_evidence} · 循环 {feedback.loop_count} · 预测误差 {prediction:.3f} · 因果证据强度 {causal:.2f} · 被动基线 {feedback.passive_count} 次 · 受阻 {feedback.blocks}（均非任务成功率）' + gpu_training + archival_health)
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
                    self.inference_deadline = 0.
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
                    self.inference_deadline = 0.
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
                self.post('status', '鼠标控制已停止，观察学习可以继续；再次控制请点击绿色按钮')
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
            self.manual_start_pending = False
            self.control_lease_active = False
            self.takeover_permission.clear()
            self.explore_permission.clear()
            self.mouse_monitor_armed.clear()
            self.control_heartbeat = 0.
            self.inference_deadline = 0.
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
            if process_mutex is not None:
                if mutex_acquired:
                    kernel32.ReleaseMutex(process_mutex)
                kernel32.CloseHandle(process_mutex)
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
                    provenance = Counter((row[14] & 0x7f) for row in self.brain.memory if len(row) > 14)
                    confirmed_frames = sum(bool(row[14] & CAPTURE_VERIFIED) for row in self.brain.memory if len(row) > 14)
                    with self.hook_event_lock:
                        attributed_events = sum(self.ai_mouse_attribution.values())
                    current_metrics = {'attributed_ai_mouse_events': attributed_events, 'autonomous_left_presses': autonomous_left_presses,
                                       'autonomous_click_scene_changes': confirmed_navigation_changes,
                                       'unique_scene_count': len(feedback.frequency),
                                       'capture_sources': {name: provenance[code] for name, code in CAPTURE_SOURCES.items()},
                                       'capture_confirmed_count': confirmed_frames,
                                       'external_task_success_rate': None,
                                       'frames': self.audit_samples, 'mean': quality, 'timestamp': time.time(), 'efficacy': feedback.efficacy_total / max(1, feedback.total), 'progress_rate': feedback.progress_effects / max(1, feedback.total), 'demonstrated_goal_matches': feedback.demonstrated_goal_matches, 'verified_goal_matches': feedback.verified_goal_matches, 'demonstrated_pointer_advances': feedback.demonstrated_pointer_advances, 'repetition_rate': feedback.repeats / max(1, feedback.total), 'blocked_rate': feedback.blocks / max(1, feedback.total), 'causal_repeats': feedback.causal_evidence, 'backend': self.brain.label if self.brain is not None else '未知'}
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
            with self.retired_lock:
                retiring = tuple(self.retired_workers)
            for task in retiring:
                if task is not threading.current_thread():
                    task.join(timeout=90.)
        except Exception as error:
            self.post('error', '关闭安装组件时出现异常：' + str(error)[:115])
        finally:
            stop_all_processes()

    def emergency_snapshot(self):
        brain = self.brain
        if brain is None:
            return
        try:
            with brain.checkpoint_lock:
                with brain.save_lock:
                    records = list(brain.memory)
                    generation = max(brain.generation, getattr(brain, 'latest_replay_generation', 0),
                                     getattr(brain, 'model_generation', 0)) + 1
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
        with self.retired_lock:
            retired_busy = any(task.is_alive() for task in self.retired_workers)
        saving = retired_busy or any(task is not None and task.is_alive() for task in (self.saver, self.exit_backup, self.shutdown_worker))
        deadline = 120. if saving else min(30., max(12., self.watchdog_limit * 4.))
        busy = any(task is not None and task.is_alive() for task in (self.worker, self.control_worker, self.saver, self.online_worker, self.acceleration_cleanup, self.acceleration_thread, self.capture_worker, self.key_thread, self.safety_thread, self.exit_backup, self.release_worker, self.initializer))
        main_busy = any(task is not None and task.is_alive() for task in (self.worker, self.saver, self.online_worker))
        if self.shutdown_worker is None and not main_busy:
            def cleanup():
                if self.brain is not None:
                    try:
                        self.brain.close()
                    except Exception as error:
                        self.exit_backup_error = '学习后端关闭异常：' + str(error)[:125]
            self.shutdown_worker = threading.Thread(target=cleanup, daemon=True)
            self.shutdown_worker.start()
        busy |= (self.shutdown_worker is not None and self.shutdown_worker.is_alive()) or retired_busy
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
