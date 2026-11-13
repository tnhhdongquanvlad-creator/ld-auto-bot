# -*- coding: utf-8 -*-
"""
LD Auto Bot - Tự động click theo hình ảnh trên LDPlayer (ADB + OpenCV)

Quy trình:
  1. Quét các tab có trong LD, chọn tab cần chạy
  2. Mở N tab cùng lúc (cách nhau vài giây) -> sắp xếp cửa sổ
  3. Mỗi tab tự chạy độc lập: cứ mỗi vài giây kiểm tra 1 ảnh theo thứ tự, thấy thì click.
     Click được ẢNH CUỐI CÙNG thì tắt tab đó. Tới ảnh cuối mà chưa thấy thì quay lại từ ảnh đầu.
  4. Tắt hết tab của đợt -> mở đợt kế tiếp cho tới hết tab
"""
import os
import re
import sys
import ctypes
import shutil
import json
import time
import queue
import threading
import subprocess
import traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

import cv2
import numpy as np
from PIL import Image, ImageTk

# ----------------------------------------------------------------------------
# Đường dẫn & cấu hình
# ----------------------------------------------------------------------------
APP_DIR = os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
TEMPLATE_DIR = os.path.join(APP_DIR, "templates")
LOG_DIR = os.path.join(APP_DIR, "logs")
CONFIG_FILE = os.path.join(APP_DIR, "config.json")
WORKFLOW_FILE = os.path.join(APP_DIR, "workflow.json")
os.makedirs(TEMPLATE_DIR, exist_ok=True)
os.makedirs(LOG_DIR, exist_ok=True)

NO_WINDOW = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0

PAL = {"bg": "#f3f4fb", "primary": "#4f46e5", "primary_d": "#4338ca", "accent": "#0ea5e9", "green": "#16a34a",
       "green_d": "#15803d", "red": "#dc2626", "red_d": "#b91c1c", "orange": "#f59e0b", "orange_d": "#d97706",
       "text": "#1f2937", "soft": "#e0e7ff"}

DEFAULT_CONFIG = {
    "ld_dir": "",
    "excluded_tabs": [],
    "batch_size": 5,          # số tab chạy cùng lúc
    "start_from_tab": 1,      # chạy từ tab số mấy trở đi
    "launch_delay": 3.0,      # giây: cách nhau khi mở tab
    "ready_timeout": 120,     # giây: chờ máy khởi động tối đa
    "step_interval": 2.0,     # giây: mỗi bước (1 ảnh) cách nhau
    "match_percent": 85,      # %: độ chính xác nhận ảnh
    "tab_timeout": 0,         # giây: tối đa mỗi tab (0 = không bao giờ tự tắt, chỉ tắt khi click được ảnh cuối)
    "cfg_version": 1,
    "stuck_scans": 30,        # quét liên tiếp N lần không thấy ảnh nào -> tắt, mở lại tab, quét lại từ đầu (0 = tắt)
    "stuck_max_restarts": 5,  # số lần mở lại tối đa cho mỗi tab
    "sort_windows": True,
    "after_sort_wait": 2.0,
    "auto_adb": True,
    "set_resolution": True,
    "res_w": 540,
    "res_h": 960,
    "res_dpi": 240,
    "post_batch_wait": 3.0,
    "test_tab": 1,
    "daily_enabled": False,   # mỗi ngày tự chạy lại từ đầu vào giờ hẹn
    "daily_hour": 6,
    "daily_minute": 0,
}

def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(default, dict):
            merged = dict(default)
            merged.update(data)
            return merged
        return data
    except Exception:
        return default


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def console_exe(d):
    if not d:
        return None
    for n in ("dnconsole.exe", "ldconsole.exe"):
        p = os.path.join(d, n)
        if os.path.isfile(p):
            return p
    return None


def find_ld_dir():
    subs = ["LDPlayer\\LDPlayer9", "LDPlayer\\LDPlayer4.0", "LDPlayer\\LDPlayer4",
            "Program Files\\LDPlayer\\LDPlayer9", "Program Files\\LDPlayer\\LDPlayer4.0",
            "LDPlayer9", "LDPlayer4.0", "LDPlayer"]
    for drive in "CDEFGH":
        for s in subs:
            p = f"{drive}:\\{s}"
            if console_exe(p):
                return p
    return ""


def is_admin():
    try:
        return ctypes.windll.shell32.IsUserAnAdmin() != 0
    except Exception:
        return False


def relaunch_as_admin():
    """dnconsole.exe của LD 9 đòi quyền Administrator (WinError 740) -> tự mở lại app với quyền admin."""
    try:
        exe = sys.executable
        args = sys.argv[1:] if getattr(sys, "frozen", False) else [os.path.abspath(__file__)] + sys.argv[1:]
        params = " ".join(f'"{a}"' for a in args)
        return ctypes.windll.shell32.ShellExecuteW(None, "runas", exe, params, APP_DIR, 1) > 32
    except Exception:
        return False


class StopRun(Exception):
    pass


class TabError(Exception):
    pass


# ----------------------------------------------------------------------------
# Điều khiển LDPlayer + ADB
# ----------------------------------------------------------------------------
class LD:
    def __init__(self, ld_dir):
        self.ld_dir = ld_dir
        self.console = console_exe(ld_dir)
        if not self.console:
            raise FileNotFoundError("Không tìm thấy dnconsole.exe / ldconsole.exe trong thư mục LD")
        self.adb = os.path.join(ld_dir, "adb.exe")
        if not os.path.isfile(self.adb):
            raise FileNotFoundError("Không tìm thấy adb.exe trong thư mục LD")
        self.serial = {}
        self.last_err = {}

    def _run(self, args, timeout=60):
        return subprocess.run(args, capture_output=True, timeout=timeout, creationflags=NO_WINDOW)

    def console_cmd(self, *args, timeout=90):
        r = self._run([self.console, *[str(a) for a in args]], timeout)
        return r.stdout.decode("utf-8", "ignore").strip()

    def start_adb_server(self):
        try:
            self._run([self.adb, "start-server"], 20)
        except Exception:
            pass

    def launch(self, i):
        self.console_cmd("launch", "--index", i)

    def quit(self, i):
        self.console_cmd("quit", "--index", i)
        self.serial.pop(i, None)

    def is_running(self, i):
        return self.console_cmd("isrunning", "--index", i).lower().startswith("running")

    def sort_windows(self):
        self.console_cmd("sortWnd", timeout=30)

    def set_resolution(self, i, w, h, dpi):
        self.console_cmd("modify", "--index", i, "--resolution", f"{w},{h},{dpi}")

    def ensure_adb_debug(self, i):
        """Bật ADB debugging (Mở kết nối cục bộ) cho máy i bằng cách sửa file vms/config/leidian{i}.config.
        Chỉ có tác dụng khi máy đang TẮT. Trả về: ok / changed / missing / error: ..."""
        path = os.path.join(self.ld_dir, "vms", "config", f"leidian{i}.config")
        if not os.path.isfile(path):
            return "missing"
        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                data = json.load(f)
            if data.get("basicSettings.adbDebug") == 1:
                return "ok"
            bak = path + ".bak"
            if not os.path.exists(bak):
                shutil.copy2(path, bak)
            data["basicSettings.adbDebug"] = 1
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
            return "changed"
        except Exception as e:
            return f"error: {e}"

    def list_instances(self):
        """Quét toàn bộ máy trong LD: [{'index','name','running'}]"""
        out = self.console_cmd("list2", timeout=30)
        res = []
        for line in out.splitlines():
            p = line.strip().split(",")
            if len(p) >= 2 and p[0].strip().isdigit():
                running = len(p) >= 5 and p[4].strip() == "1"
                res.append({"index": int(p[0]), "name": p[1].strip(), "running": running})
        return sorted(res, key=lambda x: x["index"])

    def adb_cmd(self, serial, *args, timeout=30, raw=False):
        r = self._run([self.adb, "-s", serial, *[str(a) for a in args]], timeout)
        return r.stdout if raw else r.stdout.decode("utf-8", "ignore").strip()

    def devices(self):
        out = self._run([self.adb, "devices"], 15).stdout.decode("utf-8", "ignore")
        res = {}
        for line in out.splitlines()[1:]:
            p = line.split()
            if len(p) >= 2:
                res[p[0]] = p[1]
        return res

    def find_serial(self, i):
        port = 5554 + 2 * i
        cands = (f"emulator-{port}", f"127.0.0.1:{port + 1}")
        devs = self.devices()
        for s in cands:
            if devs.get(s) == "device":
                return s
        try:
            self._run([self.adb, "connect", f"127.0.0.1:{port + 1}"], 10)
        except Exception:
            pass
        devs = self.devices()
        for s in cands:
            if devs.get(s) == "device":
                return s
        return None

    def wait_ready(self, i, timeout, stop_ev=None, log=None):
        start = time.time()
        end = start + timeout
        last = time.time()
        while time.time() < end:
            if stop_ev is not None and stop_ev.is_set():
                return None
            try:
                if self.is_running(i):
                    s = self.find_serial(i)
                    if s and self.adb_cmd(s, "shell", "getprop", "sys.boot_completed", timeout=10).strip() == "1":
                        self.serial[i] = s
                        return s
            except Exception:
                pass
            if log and time.time() - last >= 15:
                last = time.time()
                try:
                    log(f"Tab {i + 1}: vẫn đang chờ máy sẵn sàng ({int(time.time() - start)}s) | "
                        f"LD báo chạy={self.is_running(i)} | ADB thấy={self.devices() or 'không có máy nào'}")
                except Exception:
                    pass
            time.sleep(2)
        if log:
            try:
                log(f"Tab {i + 1}: HẾT GIỜ chờ. ADB đang thấy: {self.devices() or 'không có máy nào'} "
                    f"(cần thấy emulator-{5554 + 2 * i} hoặc 127.0.0.1:{5555 + 2 * i})")
            except Exception:
                pass
        return None

    @staticmethod
    def _decode(data):
        if not data:
            return None
        try:
            img = cv2.imdecode(np.frombuffer(data, np.uint8), cv2.IMREAD_COLOR)
            if img is None:
                img = cv2.imdecode(np.frombuffer(data.replace(b"\r\n", b"\n"), np.uint8), cv2.IMREAD_COLOR)
            return img
        except Exception:
            return None

    def _screenshot_pull(self, i, s):
        """Cách dự phòng cho adb/Android đời cũ: chụp vào /sdcard rồi pull về."""
        remote = "/sdcard/_ldbot_shot.png"
        local = os.path.join(LOG_DIR, f"_shot_tab{i + 1}.png")
        try:
            if os.path.isfile(local):
                os.remove(local)
            self.adb_cmd(s, "shell", "screencap", "-p", remote, timeout=25)
            self._run([self.adb, "-s", s, "pull", remote, local], 30)
            if os.path.isfile(local):
                return cv2.imdecode(np.fromfile(local, dtype=np.uint8), cv2.IMREAD_COLOR)
        except Exception as e:
            self.last_err[i] = f"cách pull lỗi: {e}"
        return None

    def screenshot(self, i):
        s = self.serial.get(i)
        if not s:
            self.last_err[i] = "chưa có kết nối ADB"
            return None
        err = ""
        try:
            r = self._run([self.adb, "-s", s, "exec-out", "screencap", "-p"], 25)
            img = self._decode(r.stdout)
            if img is not None:
                return img
            err = f"exec-out trả về {len(r.stdout)} byte, stderr: {(r.stderr or b'').decode('utf-8', 'ignore').strip()[:200]}"
        except Exception as e:
            err = f"exec-out lỗi: {e}"
        img = self._screenshot_pull(i, s)
        if img is not None:
            return img
        self.last_err[i] = (err + " | " + self.last_err.get(i, "")).strip(" |")
        return None

    def tap(self, i, x, y):
        """Click 1 điểm. Trả về True nếu lệnh tap chạy thành công."""
        s = self.serial.get(i)
        if not s:
            return False
        try:
            r = self._run([self.adb, "-s", s, "shell", "input", "tap", str(int(x)), str(int(y))], 15)
            return r.returncode == 0
        except Exception:
            return False


# ----------------------------------------------------------------------------
# Nhận diện hình ảnh
# ----------------------------------------------------------------------------
class Vision:
    cache = {}
    lock = threading.Lock()

    @classmethod
    def load(cls, name):
        path = os.path.join(TEMPLATE_DIR, name)
        mt = os.path.getmtime(path)
        with cls.lock:
            c = cls.cache.get(name)
            if c and c[0] == mt:
                return c[1]
            img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_COLOR)
            if img is None:
                raise FileNotFoundError(f"Không đọc được ảnh mẫu: {name}")
            cls.cache[name] = (mt, img)
            return img

    @staticmethod
    def find(screen, tpl, thr):
        if screen is None or tpl is None:
            return None
        th, tw = tpl.shape[:2]
        sh, sw = screen.shape[:2]
        if th > sh or tw > sw:
            return None
        res = cv2.matchTemplate(screen, tpl, cv2.TM_CCOEFF_NORMED)
        _, mx, _, loc = cv2.minMaxLoc(res)
        if mx >= thr:
            return loc[0] + tw // 2, loc[1] + th // 2, float(mx)
        return None


def load_steps():
    """workflow.json: danh sách ảnh theo thứ tự [{"image": "ten.png"}, ...]
    (tự chuyển đổi từ định dạng cũ: chỉ giữ các bước có ảnh)."""
    raw = load_json(WORKFLOW_FILE, [])
    steps = []
    if isinstance(raw, list):
        for st in raw:
            if isinstance(st, dict) and st.get("image"):
                steps.append({"image": st["image"]})
    return steps


# ----------------------------------------------------------------------------
# Bộ chạy theo đợt
# ----------------------------------------------------------------------------
class Runner:
    def __init__(self, cfg, steps, log, progress, stop_ev, pause_ev, skip_ev):
        self.cfg = cfg
        self.steps = steps
        self.log = log
        self.progress = progress
        self.stop = stop_ev
        self.pause = pause_ev
        self.skip = skip_ev
        self.ld = LD(cfg["ld_dir"])
        self.thr = float(cfg["match_percent"]) / 100.0
        self.fails = {}
        self.popups = sorted(f for f in os.listdir(TEMPLATE_DIR)
                             if f.lower().startswith("popup_") and f.lower().endswith(".png"))

    # ---- tiện ích điều khiển luồng
    def check(self):
        while self.pause.is_set() and not self.stop.is_set():
            time.sleep(0.3)
        if self.stop.is_set():
            raise StopRun()

    def sleep(self, sec):
        end = time.time() + float(sec)
        while True:
            self.check()
            left = end - time.time()
            if left <= 0:
                return
            time.sleep(min(0.25, left))

    def shot(self, i):
        img = self.ld.screenshot(i)
        if img is None:
            t0 = self.fails.setdefault(i, time.time())
            if time.time() - t0 >= 120:
                raise TabError("không chụp được màn hình suốt 120 giây (mất kết nối ADB hoặc máy bị treo)")
        else:
            self.fails.pop(i, None)
        return img

    def handle_popups(self, i, screen):
        for name in self.popups:
            m = Vision.find(screen, Vision.load(name), self.thr)
            if m:
                self.ld.tap(i, m[0], m[1])
                self.log(f"Tab {i + 1}: đóng popup '{name}'")
                self.sleep(0.8)
                return True
        return False

    def prepare_adb(self, i):
        tab = i + 1
        if self.ld.is_running(i):
            self.log(f"Tab {tab}: đang mở sẵn nên không sửa được cài đặt ADB "
                     f"(nếu lỗi kết nối ADB, hãy tắt tab rồi chạy lại)")
            return
        r = self.ld.ensure_adb_debug(i)
        if r == "changed":
            self.log(f"Tab {tab}: đã tự bật ADB debugging")
        elif r == "ok":
            self.log(f"Tab {tab}: ADB debugging đã bật sẵn")
        elif r == "missing":
            self.log(f"Tab {tab}: không thấy file cấu hình leidian{i}.config, bỏ qua bước bật ADB")
        else:
            self.log(f"Tab {tab}: không bật được ADB tự động ({r})")

    # ---- giai đoạn MỞ 1 tab
    def open_tab(self, i, order):
        tab = i + 1
        try:
            self.sleep(order * float(self.cfg["launch_delay"]))
            if self.cfg["set_resolution"] and not self.ld.is_running(i):
                self.ld.set_resolution(i, self.cfg["res_w"], self.cfg["res_h"], self.cfg["res_dpi"])
            if self.cfg.get("auto_adb", True):
                self.prepare_adb(i)
            self.log(f"Tab {tab}: đang mở...")
            self.ld.launch(i)
            if not self.ld.wait_ready(i, float(self.cfg["ready_timeout"]), self.stop, self.log):
                self.check()
                raise TabError("máy không khởi động được trong thời gian cho phép")
            self.log(f"Tab {tab}: đã sẵn sàng")
            return True
        except StopRun:
            return False
        except TabError as e:
            self.log(f"Tab {tab}: LỖI - {e}")
            return False
        except Exception:
            self.log(f"Tab {tab}: LỖI không mong muốn\n{traceback.format_exc()}")
            return False

    # ---- click ảnh cuối: lệnh tap chạy thành công là tính thành công
    def click_final(self, i, m, tries=3):
        for _ in range(tries):
            if self.ld.tap(i, m[0], m[1]):
                return True
            self.sleep(1)
        return False

    # ---- 1 tab chạy ĐỘC LẬP
    def scan_tab(self, i, deadline):
        """Mỗi 'step_interval' giây: chụp màn hình 1 lần, tìm TẤT CẢ ảnh trên ảnh chụp đó.
        Ảnh cuối thấy -> click và tắt tab. Không thì click ảnh đầu tiên thấy theo thứ tự #1..N-1."""
        tab = i + 1
        imgs = [(n, st["image"], Vision.load(st["image"])) for n, st in enumerate(self.steps, 1)]
        total = len(imgs)
        order = [imgs[-1]] + imgs[:-1]          # ưu tiên ảnh cuối, rồi #1..#N-1
        gap = max(0.5, float(self.cfg["step_interval"]))
        clicks = rounds = 0
        empty = restarts = 0
        stuck_n = int(self.cfg.get("stuck_scans", 0))
        stuck_max = int(self.cfg.get("stuck_max_restarts", 5))
        start = last_hb = time.time()
        try:
            while True:
                rounds += 1
                self.check()
                if self.skip.is_set():
                    self.log(f"Tab {tab}: dừng quét theo yêu cầu bỏ qua đợt (đã click {clicks} lần)")
                    return False
                if deadline and time.time() >= deadline:
                    self.log(f"Tab {tab}: HẾT GIỜ ({int(self.cfg['tab_timeout'])} giây) mà chưa click được "
                             f"ảnh cuối (đã click {clicks} lần, quét {rounds} lần)")
                    return False
                screen = self.shot(i)
                hit = None
                if screen is not None:
                    for n, name, tpl in order:
                        m = Vision.find(screen, tpl, self.thr)
                        if m:
                            hit = (n, name, m)
                            break
                    if hit is None and self.popups and self.handle_popups(i, screen):
                        empty = 0
                    elif hit is None:
                        empty += 1
                    else:
                        empty = 0
                    if stuck_n > 0 and empty >= stuck_n and restarts < stuck_max:
                        restarts += 1
                        self.log(f"Tab {tab}: quét {empty} lần liên tiếp không thấy ảnh nào -> "
                                 f"MỞ LẠI TAB, quét lại từ đầu (lần {restarts}/{stuck_max})")
                        try:
                            name = f"stuck_tab{tab}_{datetime.now():%H%M%S}.png"
                            cv2.imencode(".png", screen)[1].tofile(os.path.join(LOG_DIR, name))
                            self.log(f"Tab {tab}: đã lưu ảnh màn hình lúc kẹt: logs\\{name}")
                        except Exception:
                            pass
                        self._safe_quit(i)
                        self.sleep(3)
                        if not self.open_tab(i, 0):
                            self.log(f"Tab {tab}: mở lại không được, dừng tab này")
                            return False
                        empty = 0
                        self.sleep(3)
                        continue
                if hit:
                    n, name, m = hit
                    if n == total:
                        if self.click_final(i, m):
                            self.log(f"Tab {tab}: ĐÃ CLICK ẢNH CUỐI '{name}' thành công -> tắt tab "
                                     f"(đã click {clicks + 1} lần, quét {rounds} lần)")
                            self._safe_quit(i)
                            return True
                        self.log(f"Tab {tab}: click ảnh cuối '{name}' bị lỗi (ADB), sẽ thử lại")
                    elif self.ld.tap(i, m[0], m[1]):
                        clicks += 1
                        self.log(f"Tab {tab}: #{n}/{total} thấy '{name}' -> click")
                if time.time() - last_hb >= 60:
                    last_hb = time.time()
                    self.log(f"Tab {tab}: đang quét... {rounds} lần, đã click {clicks} lần "
                             f"({int(time.time() - start)} giây)")
                self.sleep(gap)
        except StopRun:
            return False
        except TabError as e:
            self.log(f"Tab {tab}: LỖI - {e} (đã click {clicks} lần)")
            return False
        except Exception:
            self.log(f"Tab {tab}: LỖI không mong muốn\n{traceback.format_exc()}")
            return False

    # ---- 1 đợt: MỞ HẾT -> SẮP XẾP -> CÁC TAB CHẠY ĐỘC LẬP
    def run_batch(self, batch, bi, total):
        with ThreadPoolExecutor(max_workers=len(batch)) as ex:
            opened = list(ex.map(lambda p: self.open_tab(p[1], p[0]), enumerate(batch)))
        ready = [i for i, ok in zip(batch, opened) if ok]
        self.log(f"Đã mở xong: {len(ready)}/{len(batch)} tab sẵn sàng")
        results = {i: False for i in batch}
        if not ready:
            return results
        self.sleep(3)  # chờ màn hình chính của máy ảo load xong
        if self.cfg.get("sort_windows", True):
            self.log("Đang sắp xếp cửa sổ các tab...")
            try:
                self.ld.sort_windows()
            except Exception as e:
                self.log(f"Không sắp xếp được cửa sổ: {e}")
            self.sleep(float(self.cfg.get("after_sort_wait", 2)))
        limit = float(self.cfg.get("tab_timeout", 0))
        deadline = time.time() + limit if limit > 0 else None
        self.log(f"BẮT ĐẦU CLICK: {len(ready)} tab chạy độc lập, {len(self.steps)} ảnh, "
                 f"mỗi bước cách nhau {float(self.cfg['step_interval']):g} giây")
        ex = ThreadPoolExecutor(max_workers=len(ready))
        try:
            futs = {i: ex.submit(self.scan_tab, i, deadline) for i in ready}
            while not all(f.done() for f in futs.values()):
                self.check()
                finished = sum(1 for f in futs.values() if f.done())
                if deadline:
                    left = max(0, int(deadline - time.time()))
                    txt = f"Đợt {bi}/{total}: xong {finished}/{len(ready)} tab, còn tối đa {left // 60}:{left % 60:02d}"
                else:
                    txt = f"Đợt {bi}/{total}: xong {finished}/{len(ready)} tab"
                self.progress(bi - 1, total, txt)
                time.sleep(0.5)
            for i, f in futs.items():
                results[i] = bool(f.result())
            return results
        finally:
            ex.shutdown(wait=False)

    def quit_batch(self, batch):
        """Tab đã click được ảnh cuối thì đã tự tắt. Ở đây chỉ dọn các tab còn mở (hết giờ / bỏ qua / dừng)."""
        try:
            left = [i for i in batch if self.ld.is_running(i)]
        except Exception:
            left = list(batch)
        if not left:
            return
        self.log(f"Tắt {len(left)} tab chưa hoàn thành (tab {', '.join(str(x + 1) for x in left)})...")
        batch = left
        with ThreadPoolExecutor(max_workers=min(len(batch), 8)) as ex:
            list(ex.map(lambda i: self._safe_quit(i), batch))
        end = time.time() + 40
        while time.time() < end:
            try:
                if not any(self.ld.is_running(i) for i in batch):
                    return
            except Exception:
                return
            time.sleep(1.5)
        self.log("Cảnh báo: một số tab chưa tắt hẳn")

    def _safe_quit(self, i):
        try:
            self.ld.quit(i)
        except Exception:
            pass

    def run(self):
        self.ld.start_adb_server()
        b = max(1, int(self.cfg["batch_size"]))
        tabs = sorted(set(int(x) for x in self.cfg["tabs"]))
        batches = [tabs[k:k + b] for k in range(0, len(tabs), b)]
        total = len(batches)
        self.log(f"Bắt đầu: {len(tabs)} tab, {b} tab cùng lúc, tổng {total} đợt")
        ok_count = fail_count = 0
        for bi, batch in enumerate(batches, 1):
            if self.stop.is_set():
                break
            self.skip.clear()
            self.progress(bi - 1, total, f"Đợt {bi}/{total}")
            self.log(f"=== ĐỢT {bi}/{total}: {len(batch)} tab ({', '.join(str(x + 1) for x in batch)}) ===")
            results = {}
            try:
                results = self.run_batch(batch, bi, total)
            except StopRun:
                pass
            finally:
                self.quit_batch(batch)
            done = sum(1 for v in results.values() if v)
            ok_count += done
            if results:
                fail_count += len(batch) - done
                self.log(f"Đợt {bi}/{total} xong: {done}/{len(batch)} tab click được ảnh cuối")
            self.progress(bi, total, f"Xong đợt {bi}/{total}")
            if not self.stop.is_set() and bi < total:
                time.sleep(float(self.cfg["post_batch_wait"]))
        if self.stop.is_set():
            self.log("ĐÃ DỪNG theo yêu cầu.")
        else:
            self.log(f"HOÀN TẤT. Click được ảnh cuối: {ok_count} tab, chưa xong/lỗi: {fail_count} tab.")


# ----------------------------------------------------------------------------
# Cửa sổ chụp ảnh mẫu / lấy tọa độ
# ----------------------------------------------------------------------------
class Picker(tk.Toplevel):
    def __init__(self, app, callback):
        super().__init__(app)
        self.app = app
        self.callback = callback
        self.title("Chụp ảnh mẫu")
        self.img = None
        self.scale = 1.0
        self.start = None
        self.rect = None

        top = ttk.Frame(self)
        top.pack(fill="x", padx=6, pady=4)
        ttk.Button(top, text="Chụp lại màn hình", command=self.refresh).pack(side="left")
        self.info = ttk.Label(top, text="  KÉO chuột quanh nút/biểu tượng cần click để cắt ảnh mẫu")
        self.info.pack(side="left", padx=8)
        self.canvas = tk.Canvas(self, cursor="crosshair", bg="#222")
        self.canvas.pack(padx=6, pady=6)
        self.canvas.bind("<ButtonPress-1>", self.on_down)
        self.canvas.bind("<B1-Motion>", self.on_move)
        self.canvas.bind("<ButtonRelease-1>", self.on_up)
        self.canvas.bind("<Motion>", self.on_hover)
        self.refresh()

    def refresh(self):
        try:
            img = self.app.test_screenshot()
        except Exception as e:
            messagebox.showerror("Lỗi", str(e), parent=self)
            return
        if img is None:
            messagebox.showerror("Lỗi", "Không chụp được màn hình tab test.", parent=self)
            return
        self.img = img
        h, w = img.shape[:2]
        self.scale = min(1.0, 780 / h, 1150 / w)
        pil = Image.fromarray(cv2.cvtColor(img, cv2.COLOR_BGR2RGB))
        pil = pil.resize((max(1, int(w * self.scale)), max(1, int(h * self.scale))))
        self.photo = ImageTk.PhotoImage(pil)
        self.canvas.config(width=self.photo.width(), height=self.photo.height())
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=self.photo)
        self.title(f"Chụp ảnh mẫu  (màn hình {w}x{h})")

    def to_img(self, x, y):
        h, w = self.img.shape[:2]
        return (min(max(int(x / self.scale), 0), w - 1), min(max(int(y / self.scale), 0), h - 1))

    def on_hover(self, e):
        if self.img is not None:
            x, y = self.to_img(e.x, e.y)
            self.info.config(text=f"  Con trỏ tại: {x}, {y}   |  KÉO chuột để cắt ảnh mẫu")

    def on_down(self, e):
        self.start = (e.x, e.y)
        if self.rect:
            self.canvas.delete(self.rect)
        self.rect = self.canvas.create_rectangle(e.x, e.y, e.x, e.y, outline="#00ff66", width=2)

    def on_move(self, e):
        if self.rect and self.start:
            self.canvas.coords(self.rect, self.start[0], self.start[1], e.x, e.y)

    def on_up(self, e):
        if self.img is None or not self.start:
            return
        dx, dy = abs(e.x - self.start[0]), abs(e.y - self.start[1])
        if dx < 5 and dy < 5:
            self.info.config(text="  Hãy KÉO chuột để chọn vùng ảnh cần click (không chỉ click 1 điểm)")
            return
        x1, y1 = self.to_img(min(self.start[0], e.x), min(self.start[1], e.y))
        x2, y2 = self.to_img(max(self.start[0], e.x), max(self.start[1], e.y))
        if x2 - x1 < 4 or y2 - y1 < 4:
            return
        name = simpledialog.askstring("Lưu ảnh mẫu", "Đặt tên ảnh mẫu (không dấu cách càng tốt):",
                                      initialvalue=f"img_{datetime.now():%H%M%S}", parent=self)
        if not name:
            return
        name = re.sub(r"[^\w\-]", "_", name.strip())
        if not name.lower().endswith(".png"):
            name += ".png"
        crop = self.img[y1:y2, x1:x2]
        cv2.imencode(".png", crop)[1].tofile(os.path.join(TEMPLATE_DIR, name))
        self.callback("template", name)
        self.info.config(text=f"  Đã lưu ảnh mẫu: {name}")




# ----------------------------------------------------------------------------
# Giao diện chính
# ----------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("LD Auto Bot")
        self.geometry("980x860")
        self.apply_theme()
        self.cfg = load_json(CONFIG_FILE, DEFAULT_CONFIG)
        if int(self.cfg.get("cfg_version", 1)) < 2:
            self.cfg["tab_timeout"] = 0   # từ bản này: tab chỉ tắt khi click được ảnh cuối
            self.cfg["cfg_version"] = 2
        self.steps = load_steps()
        self.log_q = queue.Queue()
        self.stop_ev = threading.Event()
        self.pause_ev = threading.Event()
        self.skip_ev = threading.Event()
        self.thread = None
        self.test_ld = None
        self.log_lock = threading.Lock()
        self.daily_last = None      # ngày đã chạy theo giờ hẹn (mỗi ngày chỉ 1 lần)
        self.pending_daily = False  # đang chờ lượt cũ dừng hẳn để chạy lại từ đầu
        if not console_exe(self.cfg["ld_dir"]):
            self.cfg["ld_dir"] = find_ld_dir()
        self.build_ui()
        self.refresh_tree()
        self.after(200, self.pump)
        self.after(1000, self.daily_tick)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        if self.cfg["ld_dir"]:
            self.after(300, lambda: self.scan(silent=True))
        else:
            self.log("Chưa tìm thấy LDPlayer. Hãy bấm 'Chọn...' để trỏ tới thư mục cài đặt LDPlayer.")

    # ---- giao diện màu sắc
    def apply_theme(self):
        P = PAL
        self.configure(bg=P["bg"])
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except Exception:
            pass
        st.configure(".", background=P["bg"], foreground=P["text"], font=("Segoe UI", 10))
        st.configure("TFrame", background=P["bg"])
        st.configure("TLabel", background=P["bg"], foreground=P["text"])
        st.configure("TLabelframe", background=P["bg"], bordercolor="#c7d2fe")
        st.configure("TLabelframe.Label", background=P["bg"], foreground=P["primary"], font=("Segoe UI", 10, "bold"))
        st.configure("TCheckbutton", background=P["bg"])
        st.configure("TRadiobutton", background=P["bg"])
        st.configure("TNotebook", background=P["bg"], borderwidth=0)
        st.configure("TNotebook.Tab", padding=(14, 8), background=P["soft"], foreground=P["primary_d"],
                     font=("Segoe UI", 10, "bold"))
        st.map("TNotebook.Tab", background=[("selected", P["primary"]), ("disabled", "#e5e7eb")],
               foreground=[("selected", "white"), ("disabled", "#9ca3af")])
        st.configure("TButton", padding=(10, 6), background=P["soft"], foreground=P["primary_d"], borderwidth=0)
        st.map("TButton", background=[("active", "#c7d2fe"), ("disabled", "#e5e7eb")],
               foreground=[("disabled", "#9ca3af")])
        for name, bg, bgd in (("Accent", P["primary"], P["primary_d"]), ("Start", P["green"], P["green_d"]),
                              ("Stop", P["red"], P["red_d"]), ("Pause", P["orange"], P["orange_d"]),
                              ("Skip", P["accent"], "#0284c7")):
            st.configure(f"{name}.TButton", background=bg, foreground="white",
                         font=("Segoe UI", 10, "bold"), padding=(12, 7))
            st.map(f"{name}.TButton", background=[("active", bgd), ("disabled", "#cbd5e1")],
                   foreground=[("disabled", "#f1f5f9")])
        st.configure("Treeview", background="white", fieldbackground="white", foreground=P["text"], rowheight=26)
        st.configure("Treeview.Heading", background=P["primary"], foreground="white",
                     font=("Segoe UI", 10, "bold"), padding=6)
        st.map("Treeview.Heading", background=[("active", P["primary_d"])])
        st.map("Treeview", background=[("selected", "#c7d2fe")], foreground=[("selected", P["text"])])
        st.configure("Horizontal.TProgressbar", troughcolor="#e5e7eb", background=P["green"], thickness=16)

    @staticmethod
    def log_tag(line):
        if any(k in line for k in ("LỖI", "HẾT GIỜ", "lỗi", "KHÔNG", "không bật được")):
            return "err"
        if any(k in line for k in ("ĐÃ CLICK ẢNH CUỐI", "HOÀN TẤT", "đã sẵn sàng", "xong:")):
            return "ok"
        if any(k in line for k in ("===", "BẮT ĐẦU", "Bắt đầu:", "HẸN GIỜ", "Đã lưu cài đặt")):
            return "head"
        if any(k in line for k in ("Cảnh báo", "Lưu ý", "dừng", "Dừng", "tạm dừng", "popup")):
            return "warn"
        if "click" in line:
            return "click"
        return ""

    def _row_tags(self, idx, pos):
        sf = self.start_from()
        info = next((x for x in self.instances if x["index"] == idx), None)
        if idx + 1 < sf or idx not in self.checked:
            return ("off",)
        if info and info["running"]:
            return ("run",)
        return ("odd",) if pos % 2 else ("even",)

    # ---- dựng giao diện
    def build_ui(self):
        self.vars = {}
        self.instances = []
        self.checked = set()

        def var(key, kind):
            v = {"s": tk.StringVar, "i": tk.IntVar, "d": tk.DoubleVar, "b": tk.BooleanVar}[kind](value=self.cfg[key])
            self.vars[key] = v
            return v

        hdr = tk.Frame(self, bg=PAL["primary"])
        hdr.pack(fill="x")
        tk.Label(hdr, text="⚡ LD AUTO BOT", bg=PAL["primary"], fg="white",
                 font=("Segoe UI", 16, "bold")).pack(side="left", padx=14, pady=8)
        tk.Label(hdr, text="Tự động click theo hình ảnh trên LDPlayer", bg=PAL["primary"], fg="#c7d2fe",
                 font=("Segoe UI", 10)).pack(side="left", pady=8)

        self.nb = ttk.Notebook(self)   # pack ở cuối build_ui để nhật ký luôn có chỗ
        p1 = ttk.Frame(self.nb, padding=6)
        p2 = ttk.Frame(self.nb, padding=2)
        self.nb.add(p1, text="  Bước 1: Quét & chọn tab LD  ")
        self.nb.add(p2, text="  Bước 2: Cài đặt & ảnh cần click  ", state="disabled")

        # ================= TRANG 1 =================
        f1 = ttk.LabelFrame(p1, text=" LDPlayer ", padding=6)
        f1.pack(fill="x")
        ttk.Label(f1, text="Thư mục LDPlayer:").pack(side="left")
        ttk.Entry(f1, textvariable=var("ld_dir", "s"), width=55).pack(side="left", padx=6)
        ttk.Button(f1, text="Chọn...", command=self.browse_ld).pack(side="left")
        ttk.Button(f1, text="Quét tab trong LD", command=self.scan).pack(side="left", padx=10)

        fl = ttk.LabelFrame(p1, text=" Danh sách tab trong LD (mặc định chạy hết; click vào dòng để bỏ chọn) ", padding=6)
        fl.pack(fill="both", expand=True, pady=6)
        self.lst = ttk.Treeview(fl, columns=("chk", "num", "name", "status"), show="headings",
                                height=9, selectmode="none")
        for c, t, w, a in (("chk", "Chọn", 60, "center"), ("num", "Tab số", 80, "center"),
                           ("name", "Tên máy trong LD", 300, "w"), ("status", "Trạng thái", 170, "center")):
            self.lst.heading(c, text=t)
            self.lst.column(c, width=w, anchor=a)
        sb1 = ttk.Scrollbar(fl, command=self.lst.yview)
        self.lst.config(yscrollcommand=sb1.set)
        self.lst.pack(side="left", fill="both", expand=True)
        sb1.pack(side="left", fill="y")
        self.lst.bind("<Button-1>", self.on_list_click)
        self.lst.tag_configure("even", background="white")
        self.lst.tag_configure("odd", background="#f5f3ff")
        self.lst.tag_configure("run", background="#dcfce7", foreground="#15803d")
        self.lst.tag_configure("off", foreground="#9ca3af")

        side = ttk.Frame(fl)
        side.pack(side="left", fill="y", padx=(8, 0))
        ttk.Button(side, text="Chọn tất cả", width=18, command=lambda: self.select_all(True)).pack(pady=2)
        ttk.Button(side, text="Bỏ chọn tất cả", width=18, command=lambda: self.select_all(False)).pack(pady=2)
        ttk.Button(side, text="Đảo lựa chọn", width=18, command=self.invert_select).pack(pady=2)
        ttk.Separator(side).pack(fill="x", pady=8)
        ttk.Label(side, text="Số tab chạy cùng lúc\n(1 - 20):", justify="center").pack()
        ttk.Spinbox(side, from_=1, to=20, textvariable=var("batch_size", "i"), width=6, justify="center").pack(pady=4)
        self.vars["batch_size"].trace_add("write", lambda *a: self.update_count())
        ttk.Label(side, text="Chạy từ tab số\n(bỏ qua tab trước đó):", justify="center").pack(pady=(10, 0))
        ttk.Spinbox(side, from_=1, to=9999, textvariable=var("start_from_tab", "i"), width=6, justify="center").pack(pady=4)
        self.vars["start_from_tab"].trace_add("write", lambda *a: self.fill_list() if self.instances else None)
        ttk.Label(side, text="Xong đợt thì tự mở\nđợt kế tiếp cho tới\nhết tab.", justify="center",
                  foreground="#666").pack(pady=8)

        bt1 = ttk.Frame(p1)
        bt1.pack(fill="x")
        self.lbl_count = ttk.Label(bt1, text="Chưa quét. Bấm 'Quét tab trong LD'.")
        self.lbl_count.pack(side="left")
        ttk.Button(bt1, text="Tiếp tục: Cài đặt & ảnh cần click  >>", command=self.go_setup,
                   style="Accent.TButton").pack(side="right")

        # ================= TRANG 2 =================
        fi = ttk.LabelFrame(p2, text=" Danh sách ảnh cần click (theo thứ tự từ trên xuống) ", padding=6)
        fi.pack(fill="both", expand=True, padx=4, pady=4)
        ttk.Label(fi, foreground="#4338ca", justify="left", wraplength=900,
                  text="Cách chạy: cứ mỗi 'Chu kỳ quét' giây, tab chụp màn hình 1 lần và tìm TẤT CẢ ảnh trong danh sách, "
                       "thấy ảnh nào thì click ảnh đó.\nClick được ảnh CUỐI CÙNG thì tab đó tắt (các tab khác vẫn chạy tiếp)."
                  ).pack(anchor="w", pady=(0, 4))
        row = ttk.Frame(fi)
        row.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(row, columns=("n", "img", "note"), show="headings", height=4)
        for c, t, w in (("n", "#", 40), ("img", "Ảnh mẫu", 260), ("note", "Ghi chú", 360)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="w")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.tag_configure("even", background="white")
        self.tree.tag_configure("odd", background="#f5f3ff")
        self.tree.tag_configure("final", background="#dcfce7", foreground="#166534")
        bf = ttk.Frame(row)
        bf.pack(side="left", fill="y", padx=(6, 0))
        for text, cmd, r, c in (("Chụp ảnh mới", self.capture_new, 0, 0), ("Chọn ảnh có sẵn", self.add_existing, 0, 1),
                                ("▲ Lên", lambda: self.move_step(-1), 1, 0), ("▼ Xuống", lambda: self.move_step(1), 1, 1),
                                ("Xóa", self.del_step, 2, 0)):
            ttk.Button(bf, text=text, command=cmd, width=15,
                       style="Accent.TButton" if text == "Chụp ảnh mới" else "TButton").grid(
                row=r, column=c, padx=2, pady=2, sticky="ew")

        fs = ttk.LabelFrame(p2, text=" Cài đặt (đơn vị: giây) ", padding=6)
        fs.pack(fill="x", padx=4, pady=4)

        def sp(label, key, kind, frm, to, r, c, inc=1, w=8):
            ttk.Label(fs, text=label).grid(row=r, column=c * 2, sticky="e", padx=(8, 2), pady=3)
            ttk.Spinbox(fs, from_=frm, to=to, increment=inc, textvariable=var(key, kind), width=w).grid(
                row=r, column=c * 2 + 1, sticky="w")

        sp("Delay mở tab (giây):", "launch_delay", "d", 0, 120, 0, 0, 0.5)
        sp("Timeout chờ khởi động (giây):", "ready_timeout", "i", 20, 900, 0, 1, 10)
        sp("Chu kỳ quét (giây):", "step_interval", "d", 0.5, 60, 1, 0, 0.5)
        sp("Độ chính xác nhận ảnh (%):", "match_percent", "i", 50, 100, 1, 1, 1)
        sp("Timeout mỗi tab (giây, 0 = không bao giờ tự tắt):", "tab_timeout", "i", 0, 86400, 2, 0, 60)
        sp("Quét N lần không thấy ảnh nào thì mở lại tab (0 = tắt):", "stuck_scans", "i", 0, 1000, 3, 0, 1)
        sp("Mở lại tối đa (lần/tab):", "stuck_max_restarts", "i", 1, 50, 3, 1, 1)

        fa = ttk.LabelFrame(p2, text=" Nâng cao ", padding=6)
        fa.pack(fill="x", padx=4, pady=4)
        ttk.Checkbutton(fa, text="Tự sắp xếp cửa sổ sau khi mở tab", variable=var("sort_windows", "b")).grid(
            row=0, column=0, sticky="w", padx=8)
        ttk.Checkbutton(fa, text="Tự bật ADB debugging cho từng tab", variable=var("auto_adb", "b")).grid(
            row=0, column=1, sticky="w", padx=8)
        ttk.Checkbutton(fa, text="Tự đặt độ phân giải:", variable=var("set_resolution", "b")).grid(
            row=1, column=0, sticky="w", padx=8)
        rf = ttk.Frame(fa)
        rf.grid(row=1, column=1, sticky="w", padx=8)
        for lab, key in (("Rộng", "res_w"), ("Cao", "res_h"), ("DPI", "res_dpi")):
            ttk.Label(rf, text=lab).pack(side="left", padx=(4, 2))
            ttk.Spinbox(rf, from_=80, to=3000, textvariable=var(key, "i"), width=6).pack(side="left")

        f4 = ttk.LabelFrame(p2, text=" Tab thử nghiệm (để chụp ảnh mẫu & chạy thử) ", padding=6)
        f4.pack(fill="x", padx=4, pady=4)
        ttk.Label(f4, text="Tab số:").pack(side="left")
        ttk.Spinbox(f4, from_=1, to=9999, textvariable=var("test_tab", "i"), width=6).pack(side="left", padx=4)
        ttk.Button(f4, text="Mở tab test", command=self.open_test).pack(side="left", padx=4)
        ttk.Button(f4, text="Tắt tab test", command=self.close_test).pack(side="left", padx=4)
        ttk.Button(f4, text="Chụp ảnh mẫu", command=lambda: self.open_picker(lambda k, d: None)).pack(side="left", padx=4)
        self.btn_try = ttk.Button(f4, text="▶ Chạy thử trên tab này", command=self.run_test, style="Accent.TButton")
        self.btn_try.pack(side="left", padx=4)
        # các khung cài đặt luôn hiện đủ; thiếu chỗ thì danh sách ảnh co lại
        for w in (fi, fs, fa, f4):
            w.pack_forget()
        for w in (f4, fa, fs):
            w.pack(side="bottom", fill="x", padx=4, pady=4)
        fi.pack(fill="both", expand=True, padx=4, pady=4)

        # ================= Điều khiển + log =================
        f5 = ttk.Frame(self)
        self.btn_start = ttk.Button(f5, text="▶ BẮT ĐẦU", command=self.start, width=14, style="Start.TButton")
        self.btn_start.pack(side="left")
        self.btn_pause = ttk.Button(f5, text="Tạm dừng", command=self.toggle_pause, width=12, state="disabled", style="Pause.TButton")
        self.btn_pause.pack(side="left", padx=6)
        self.btn_stop = ttk.Button(f5, text="■ Dừng", command=self.stop, width=10, state="disabled", style="Stop.TButton")
        self.btn_stop.pack(side="left")
        self.btn_skip = ttk.Button(f5, text="⏭ Bỏ qua đợt này", command=self.skip_batch, width=18, state="disabled", style="Skip.TButton")
        self.btn_skip.pack(side="left", padx=6)
        self.lbl_prog = ttk.Label(f5, text="Chưa chạy")
        self.lbl_prog.pack(side="left", padx=12)
        self.pb = ttk.Progressbar(f5, length=240)
        self.pb.pack(side="left")
        ttk.Button(f5, text="💾 Lưu cài đặt", command=self.save_settings, width=14,
                   style="Accent.TButton").pack(side="right")

        f7 = ttk.Frame(self)
        ttk.Checkbutton(f7, text="⏰ Mỗi ngày tự chạy lại từ đầu lúc", variable=var("daily_enabled", "b")).pack(side="left")
        ttk.Spinbox(f7, from_=0, to=23, wrap=True, textvariable=var("daily_hour", "i"), width=4,
                    justify="center").pack(side="left", padx=(6, 2))
        ttk.Label(f7, text="giờ").pack(side="left")
        ttk.Spinbox(f7, from_=0, to=59, wrap=True, textvariable=var("daily_minute", "i"), width=4,
                    justify="center").pack(side="left", padx=(6, 2))
        ttk.Label(f7, text="phút").pack(side="left")
        self.lbl_daily = ttk.Label(f7, text="")
        self.lbl_daily.pack(side="left", padx=12)
        for k in ("daily_enabled", "daily_hour", "daily_minute"):
            self.vars[k].trace_add("write", lambda *a: self.daily_label())

        f6 = ttk.LabelFrame(self, text=" Nhật ký ", padding=4)
        self.logbox = tk.Text(f6, height=5, wrap="word", font=("Consolas", 10), bg="#0f172a", fg="#e2e8f0",
                              insertbackground="white", relief="flat", padx=8, pady=6)
        for tag, color in (("ok", "#4ade80"), ("err", "#f87171"), ("warn", "#fbbf24"),
                           ("head", "#22d3ee"), ("click", "#93c5fd")):
            self.logbox.tag_configure(tag, foreground=color)
        self.logbox.tag_configure("head", foreground="#22d3ee", font=("Consolas", 10, "bold"))
        sb = ttk.Scrollbar(f6, command=self.logbox.yview)
        self.logbox.config(yscrollcommand=sb.set)
        self.logbox.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")

        # xếp từ dưới lên: nhật ký, hẹn giờ, nút điều khiển; phần còn lại cho 2 trang Bước 1/Bước 2
        f6.pack(side="bottom", fill="x", padx=8, pady=(4, 8))
        f7.pack(side="bottom", fill="x", padx=8, pady=(0, 2))
        f5.pack(side="bottom", fill="x", padx=8, pady=4)
        self.nb.pack(fill="both", expand=True, padx=8, pady=(8, 4))

    # ---- quét & chọn tab
    def scan(self, silent=False):
        d = self.vars["ld_dir"].get()
        if not console_exe(d):
            if not silent:
                messagebox.showerror("Lỗi", "Chưa chọn đúng thư mục LDPlayer (cần có dnconsole.exe hoặc ldconsole.exe).")
            return
        try:
            inst = self.get_ld().list_instances()
        except Exception as e:
            if not silent:
                hint = ""
                if getattr(e, "winerror", None) == 740:
                    hint = "\n\nCần chạy app bằng quyền Administrator (chuột phải > Run as administrator)."
                messagebox.showerror("Lỗi", f"Không quét được danh sách tab:\n{e}{hint}")
            return
        if not inst:
            if not silent:
                messagebox.showerror("Lỗi", "Không thấy máy nào trong LD. Hãy tạo máy trong LD Multiplayer rồi quét lại.")
            return
        self.instances = inst
        ids = {i["index"] for i in inst}
        self.checked = set(ids) - set(self.cfg.get("excluded_tabs") or [])
        if not self.checked:
            self.checked = set(ids)
        self.fill_list()
        self.nb.tab(1, state="normal")
        self.log(f"Đã quét: tìm thấy {len(inst)} tab trong LD (tab {min(ids) + 1} - {max(ids) + 1}).")

    def start_from(self):
        try:
            return max(1, int(self.vars["start_from_tab"].get()))
        except Exception:
            return 1

    def fill_list(self):
        sf = self.start_from()
        self.lst.delete(*self.lst.get_children())
        for pos, i in enumerate(self.instances):
            idx = i["index"]
            status = "Đang chạy" if i["running"] else "Tắt"
            if idx + 1 < sf:
                status = f"Bỏ qua (trước tab {sf})"
            elif idx not in self.checked:
                status = "Không chạy"
            self.lst.insert("", "end", iid=str(idx), tags=self._row_tags(idx, pos), values=(
                "☑" if idx in self.checked else "☐", idx + 1, i["name"], status))
        self.update_count()

    def update_count(self):
        if not hasattr(self, "lbl_count"):
            return
        sf = self.start_from()
        n, total = len(self.checked), len(self.instances)
        n_run = sum(1 for x in self.checked if x + 1 >= sf)
        plan = ""
        try:
            b = max(1, int(self.vars["batch_size"].get()))
            if n_run:
                plan = f"   →   sẽ chạy {n_run} tab (từ tab {sf}), {min(b, n_run)} tab cùng lúc, tổng {-(-n_run // b)} đợt"
            else:
                plan = f"   →   không có tab nào để chạy (từ tab {sf} trở đi)"
        except Exception:
            pass
        self.lbl_count.config(text=f"Đã chọn {n} / {total} tab{plan}")

    def on_list_click(self, e):
        iid = self.lst.identify_row(e.y)
        if iid:
            idx = int(iid)
            self.checked.symmetric_difference_update({idx})
            self.lst.set(iid, "chk", "☑" if idx in self.checked else "☐")
            self.lst.item(iid, tags=self._row_tags(idx, self.lst.index(iid)))
            self.update_count()
        return "break"

    def select_all(self, state):
        self.checked = {i["index"] for i in self.instances} if state else set()
        self.fill_list()

    def invert_select(self):
        self.checked = {i["index"] for i in self.instances} - self.checked
        self.fill_list()

    def save_selection(self):
        ids = {i["index"] for i in self.instances}
        self.cfg["excluded_tabs"] = sorted(ids - self.checked)

    def go_setup(self):
        if not self.checked:
            messagebox.showerror("Lỗi", "Chưa chọn tab nào. Hãy tick ít nhất 1 tab.")
            return
        self.save_selection()
        self.nb.select(1)

    def browse_ld(self):
        d = filedialog.askdirectory(title="Chọn thư mục cài đặt LDPlayer (chứa dnconsole.exe hoặc ldconsole.exe)")
        if d:
            d = d.replace("/", "\\")
            if not console_exe(d):
                messagebox.showerror("Lỗi", "Thư mục này không có dnconsole.exe hoặc ldconsole.exe.")
                return
            self.vars["ld_dir"].set(d)
            self.scan()

    # ---- danh sách ảnh cần click
    def refresh_tree(self, select=None):
        self.tree.delete(*self.tree.get_children())
        n_total = len(self.steps)
        for n, st in enumerate(self.steps, 1):
            note = "ẢNH CUỐI: click được là tắt tab" if n == n_total else "click rồi sang ảnh kế tiếp"
            tag = "final" if n == n_total else ("odd" if n % 2 else "even")
            self.tree.insert("", "end", iid=str(n - 1), tags=(tag,), values=(n, st["image"], note))
        if select is not None and 0 <= select < len(self.steps):
            self.tree.selection_set(str(select))
        save_json(WORKFLOW_FILE, self.steps)

    def selected(self):
        sel = self.tree.selection()
        return int(sel[0]) if sel else None

    def capture_new(self):
        def cb(kind, data):
            if kind == "template":
                self.steps.append({"image": data})
                self.refresh_tree(len(self.steps) - 1)
        self.open_picker(cb)

    def add_existing(self):
        f = filedialog.askopenfilename(title="Chọn ảnh mẫu", initialdir=TEMPLATE_DIR,
                                       filetypes=[("Ảnh", "*.png *.jpg *.jpeg *.bmp")])
        if not f:
            return
        name = os.path.basename(f)
        dest = os.path.join(TEMPLATE_DIR, name)
        if os.path.abspath(f) != os.path.abspath(dest):
            shutil.copy2(f, dest)
        self.steps.append({"image": name})
        self.refresh_tree(len(self.steps) - 1)

    def del_step(self):
        idx = self.selected()
        if idx is not None and messagebox.askyesno("Xóa", "Xóa ảnh đã chọn khỏi danh sách?"):
            del self.steps[idx]
            self.refresh_tree(min(idx, len(self.steps) - 1))

    def move_step(self, d):
        idx = self.selected()
        if idx is None:
            return
        j = idx + d
        if 0 <= j < len(self.steps):
            self.steps[idx], self.steps[j] = self.steps[j], self.steps[idx]
            self.refresh_tree(j)

    # ---- cấu hình
    def collect_cfg(self):
        c = dict(self.cfg)
        for k, v in self.vars.items():
            c[k] = v.get()
        return c

    # ---- log
    def log(self, msg):
        line = f"[{datetime.now():%H:%M:%S}] {msg}"
        self.log_q.put(("log", line))
        try:
            with self.log_lock:
                with open(os.path.join(LOG_DIR, f"run_{datetime.now():%Y%m%d}.log"), "a", encoding="utf-8") as f:
                    f.write(line + "\n")
        except Exception:
            pass

    def progress(self, v, mx, text):
        self.log_q.put(("progress", v, mx, text))

    def pump(self):
        try:
            while True:
                m = self.log_q.get_nowait()
                if m[0] == "log":
                    tag = self.log_tag(m[1])
                    self.logbox.insert("end", m[1] + "\n", (tag,) if tag else ())
                    self.logbox.see("end")
                    if int(self.logbox.index("end-1c").split(".")[0]) > 3000:
                        self.logbox.delete("1.0", "1000.0")
                elif m[0] == "progress":
                    self.pb["maximum"] = max(1, m[2])
                    self.pb["value"] = m[1]
                    self.lbl_prog.config(text=m[3])
                elif m[0] == "done":
                    self.set_running(False)
                    if self.pending_daily:
                        self.pending_daily = False
                        self.log("⏰ HẸN GIỜ: lượt cũ đã dừng, 5 giây nữa chạy lại từ đầu")
                        self.after(5000, lambda: self.start(auto=True))
        except queue.Empty:
            pass
        self.after(200, self.pump)

    def set_running(self, running):
        self.btn_start.config(state="disabled" if running else "normal")
        self.btn_try.config(state="disabled" if running else "normal")
        self.btn_pause.config(state="normal" if running else "disabled", text="Tạm dừng")
        self.btn_stop.config(state="normal" if running else "disabled")
        self.btn_skip.config(state="normal" if running else "disabled")

    # ---- đọc & kiểm tra cài đặt trên giao diện
    def read_cfg(self, err):
        try:
            cfg = self.collect_cfg()
        except tk.TclError:
            err("Có ô số đang để trống hoặc sai định dạng.")
            return None
        cfg["batch_size"] = min(20, max(1, int(cfg["batch_size"])))
        cfg["step_interval"] = min(60.0, max(0.5, float(cfg["step_interval"])))
        cfg["match_percent"] = min(100, max(50, int(cfg["match_percent"])))
        cfg["tab_timeout"] = max(0, int(cfg["tab_timeout"]))
        cfg["stuck_scans"] = max(0, int(cfg["stuck_scans"]))
        cfg["stuck_max_restarts"] = max(1, int(cfg["stuck_max_restarts"]))
        cfg["daily_hour"] = min(23, max(0, int(cfg["daily_hour"])))
        cfg["daily_minute"] = min(59, max(0, int(cfg["daily_minute"])))
        for k in ("batch_size", "step_interval", "match_percent", "tab_timeout", "daily_hour", "daily_minute"):
            self.vars[k].set(cfg[k])
        if self.instances:
            cfg["excluded_tabs"] = sorted({i["index"] for i in self.instances} - self.checked)
        return cfg

    # ---- nút Lưu cài đặt
    def save_settings(self):
        cfg = self.read_cfg(lambda m: messagebox.showerror("Lỗi", m))
        if cfg is None:
            return
        self.cfg = dict(cfg)
        try:
            save_json(CONFIG_FILE, self.cfg)
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không lưu được cài đặt:\n{e}")
            return
        daily = (f"mỗi ngày tự chạy lại lúc {cfg['daily_hour']:02d}:{cfg['daily_minute']:02d}"
                 if cfg.get("daily_enabled") else "hẹn giờ đang tắt")
        self.log(f"💾 Đã lưu cài đặt ({cfg['batch_size']} tab cùng lúc, chạy từ tab {cfg['start_from_tab']}, {daily})")

    # ---- hẹn giờ chạy lại mỗi ngày
    def daily_target(self):
        """Trả về (bật?, giờ hẹn của hôm nay) theo các ô trên giao diện."""
        try:
            on = bool(self.vars["daily_enabled"].get())
            h, m = int(self.vars["daily_hour"].get()), int(self.vars["daily_minute"].get())
        except (tk.TclError, ValueError):
            return False, None
        if not on or not (0 <= h <= 23 and 0 <= m <= 59):
            return False, None
        return True, datetime.now().replace(hour=h, minute=m, second=0, microsecond=0)

    def daily_label(self):
        on, target = self.daily_target()
        if not on:
            self.lbl_daily.config(text="(đang tắt)", foreground="#9ca3af")
            return
        now = datetime.now()
        nxt = target if (now < target and self.daily_last != now.date()) else target + timedelta(days=1)
        self.lbl_daily.config(text=f"→ lần tự chạy kế tiếp: {nxt:%H:%M} ngày {nxt:%d/%m}  (app phải luôn mở)",
                              foreground=PAL["green_d"])

    def daily_tick(self):
        on, target = self.daily_target()
        now = datetime.now()
        if on and self.daily_last != now.date() and timedelta(0) <= now - target < timedelta(minutes=5):
            self.daily_last = now.date()
            self.fire_daily()
        self.daily_label()
        self.after(10000, self.daily_tick)

    def fire_daily(self):
        self.log(f"⏰ HẸN GIỜ {datetime.now():%H:%M}: đến giờ chạy lại từ đầu")
        if self.thread and self.thread.is_alive():
            self.log("⏰ HẸN GIỜ: lượt trước chưa xong -> dừng lại, tắt các tab đang mở rồi chạy lại từ đầu")
            self.pending_daily = True
            self.stop_ev.set()
            self.pause_ev.clear()
        else:
            self.start(auto=True)

    # ---- chạy
    def start(self, only_tab=None, auto=False):
        """auto=True: chạy theo giờ hẹn, không hiện hộp thoại (không có ai ở máy để bấm), lỗi ghi vào nhật ký."""
        if self.thread and self.thread.is_alive():
            return

        def err(msg):
            if auto:
                self.log(f"⏰ HẸN GIỜ: LỖI, không chạy được - {msg}")
            else:
                messagebox.showerror("Lỗi", msg)

        if auto:
            # quét lại danh sách tab trong LD (giữ đúng các tab đã chọn)
            if self.instances:
                self.save_selection()
            self.scan(silent=True)
            if not self.instances:
                err("không quét được danh sách tab trong LD")
                return
        cfg = self.read_cfg(err)
        if cfg is None:
            return
        if not console_exe(cfg["ld_dir"]):
            err("Chưa chọn đúng thư mục LDPlayer.")
            return
        sf = self.start_from()
        tabs = [only_tab - 1] if only_tab else [x for x in sorted(self.checked) if x + 1 >= sf]
        if not tabs:
            err(f"Không có tab nào để chạy. Kiểm tra các tab đã tick ở Bước 1 "
                f"và ô 'Chạy từ tab số' (đang là {sf}).")
            return
        if not self.steps:
            err("Danh sách ảnh đang trống. Hãy thêm ít nhất 1 ảnh (ảnh cuối cùng là ảnh kết thúc).")
            return
        for st in self.steps:
            if not os.path.isfile(os.path.join(TEMPLATE_DIR, st["image"])):
                err(f"Thiếu ảnh mẫu: {st['image']}\n(trong thư mục templates)")
                return
        if not only_tab and not auto:
            try:
                busy = [i["index"] + 1 for i in self.get_ld().list_instances()
                        if i["running"] and i["index"] in tabs]
            except Exception:
                busy = []
            if busy and not messagebox.askyesno(
                    "Có tab đang mở",
                    f"Đang có {len(busy)} tab được chọn đang mở (tab {', '.join(map(str, busy[:15]))}"
                    f"{'...' if len(busy) > 15 else ''}).\nApp sẽ tắt chúng khi xong đợt. Tiếp tục?"):
                return
        if auto:
            self.log(f"⏰ HẸN GIỜ: bắt đầu chạy lại từ đầu ({len(tabs)} tab, từ tab {sf})")
        self.save_selection()
        self.cfg = dict(cfg)
        save_json(CONFIG_FILE, self.cfg)
        run_cfg = dict(cfg)
        run_cfg["tabs"] = tabs
        if only_tab:
            run_cfg["batch_size"] = 1
        self.stop_ev.clear()
        self.pause_ev.clear()
        self.skip_ev.clear()
        self.pb["value"] = 0
        self.set_running(True)
        self.thread = threading.Thread(target=self._worker, args=(run_cfg, list(self.steps)), daemon=True)
        self.thread.start()

    def _worker(self, cfg, steps):
        try:
            Runner(cfg, steps, self.log, self.progress, self.stop_ev, self.pause_ev, self.skip_ev).run()
        except Exception:
            self.log("LỖI nghiêm trọng:\n" + traceback.format_exc())
        finally:
            self.log_q.put(("done",))

    def run_test(self):
        try:
            self.start(only_tab=int(self.vars["test_tab"].get()))
        except tk.TclError:
            pass

    def toggle_pause(self):
        if self.pause_ev.is_set():
            self.pause_ev.clear()
            self.btn_pause.config(text="Tạm dừng")
            self.log("Tiếp tục chạy")
        else:
            self.pause_ev.set()
            self.btn_pause.config(text="Tiếp tục")
            self.log("Đã tạm dừng")

    def stop(self):
        self.pending_daily = False
        self.stop_ev.set()
        self.pause_ev.clear()
        self.log("Đang dừng, sẽ tắt các tab của đợt hiện tại...")

    def skip_batch(self):
        self.skip_ev.set()
        self.log("Yêu cầu bỏ qua đợt hiện tại: các tab sẽ ngừng quét và được tắt")

    # ---- tab test & picker
    def get_ld(self):
        d = self.vars["ld_dir"].get()
        if self.test_ld is None or self.test_ld.console != console_exe(d):
            self.test_ld = LD(d)
        return self.test_ld

    def open_test(self):
        try:
            ld = self.get_ld()
            i = int(self.vars["test_tab"].get()) - 1
            c = self.collect_cfg()
        except Exception as e:
            messagebox.showerror("Lỗi", str(e))
            return

        def job():
            try:
                ld.start_adb_server()
                if c["set_resolution"] and not ld.is_running(i):
                    ld.set_resolution(i, c["res_w"], c["res_h"], c["res_dpi"])
                if c.get("auto_adb", True) and not ld.is_running(i):
                    self.log(f"Tab test {i + 1}: bật ADB tự động -> {ld.ensure_adb_debug(i)}")
                self.log(f"Đang mở tab test {i + 1}...")
                ld.launch(i)
                if ld.wait_ready(i, float(c["ready_timeout"]), log=self.log):
                    self.log(f"Tab test {i + 1} đã sẵn sàng. Chờ khoảng 30 giây cho màn hình load xong rồi bấm 'Chụp ảnh mẫu'.")
                else:
                    self.log(f"Tab test {i + 1} không khởi động được.")
            except Exception as e:
                self.log(f"Lỗi mở tab test: {e}")
        threading.Thread(target=job, daemon=True).start()

    def close_test(self):
        try:
            ld = self.get_ld()
            i = int(self.vars["test_tab"].get()) - 1
        except Exception as e:
            messagebox.showerror("Lỗi", str(e))
            return
        threading.Thread(target=lambda: (ld.quit(i), self.log(f"Đã tắt tab test {i + 1}")), daemon=True).start()

    def test_screenshot(self):
        ld = self.get_ld()
        i = int(self.vars["test_tab"].get()) - 1
        s = ld.find_serial(i)
        if not s:
            raise RuntimeError("Tab test chưa chạy hoặc ADB chưa kết nối.\n"
                               "Hãy bấm 'Mở tab test', chờ máy khởi động xong rồi thử lại.")
        ld.serial[i] = s
        boot = ld.adb_cmd(s, "shell", "getprop", "sys.boot_completed", timeout=10).strip()
        if boot != "1":
            raise RuntimeError("Máy ảo chưa khởi động xong (màn hình còn đang tải).\n"
                               "Chờ thêm 20-30 giây rồi bấm 'Chụp lại màn hình'.")
        img = ld.screenshot(i)
        if img is None:
            raise RuntimeError("Không chụp được màn hình tab test.\n"
                               f"Kết nối ADB: {s}\nChi tiết: {ld.last_err.get(i, 'không rõ')}")
        return img

    def open_picker(self, callback):
        Picker(self, callback)

    def on_close(self):
        if self.thread and self.thread.is_alive():
            if not messagebox.askyesno("Thoát", "App đang chạy. Dừng và thoát?"):
                return
            self.stop_ev.set()
        self.destroy()


if __name__ == "__main__":
    if os.name == "nt" and not is_admin():
        if relaunch_as_admin():
            sys.exit(0)
    App().mainloop()
