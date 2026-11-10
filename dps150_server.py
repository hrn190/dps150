#!/usr/bin/env python3
"""
DPS-150 LAN sunucusu
====================

DPS-150'yi bu bilgisayarda seri porttan okur, ölçümleri diske kaydeder ve ölçüm sayfasını
yerel ağa yayınlar. Aynı ağdaki her bilgisayar/telefon http://<bu-pc-ip>:8150 adresinden
canlı veriyi görür, kaydı başlatıp durdurabilir, çıkışı açıp kapatabilir.
Kayıt sunucuda sürdüğü için tarayıcıyı kapatmak kaydı durdurmaz.

Kullanım:
  python dps150_server.py                       # sunucuyu başlat, kaydı sayfadan başlat
  python dps150_server.py --port COM7 --baslat  # açılır açılmaz COM7'den kayda başla
  python dps150_server.py --http-port 8150 --no-rtscts

Gereksinim: Python 3.8+ ve pyserial  (pip install pyserial)
Ölçümler bu klasördeki dps150_kayit.bin dosyasında tutulur; "Kaydı sil" eski dosyayı
arsiv/ klasörüne taşır.
Protokol: github.com/cho45/fnirsi-dps-150 (resmi değildir).
"""

import argparse
import bisect
import json
import math
import os
import queue
import socket
import struct
import sys
import threading
import time
from array import array
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
ROW = 8  # t, V, A, W, Vin, sıcaklık, mod(1 CV, 0 CC, -1 ?), koruma

# ---------------------------------------------------------------- protokol
HDR_TX, HDR_RX = 0xF1, 0xF0
CMD_GET, CMD_BAUD, CMD_SESSION = 0xA1, 0xB0, 0xC1
T_VIN, T_OUT, T_TEMP = 0xC0, 0xC3, 0xC4
T_OUT_ON, T_PROT, T_MODE = 0xDB, 0xDC, 0xDD
T_MODEL, T_HW, T_FW, T_ALL = 0xDE, 0xDF, 0xE0, 0xFF
BAUDS = [9600, 19200, 38400, 57600, 115200]


def make_packet(cmd, typ, data=b""):
    if isinstance(data, int):
        data = bytes([data])
    return bytes([HDR_TX, cmd, typ, len(data)]) + data + bytes([(typ + len(data) + sum(data)) % 256])


class FrameParser:
    def __init__(self):
        self.buf = bytearray()

    def feed(self, chunk):
        self.buf.extend(chunk)
        out = []
        while True:
            i = self.buf.find(bytes([HDR_RX]))
            if i < 0:
                self.buf.clear()
                break
            if i:
                del self.buf[:i]
            if len(self.buf) < 5:
                break
            ln = self.buf[3]
            if len(self.buf) < 5 + ln:
                break
            typ = self.buf[2]
            data = bytes(self.buf[4:4 + ln])
            if (typ + ln + sum(data)) % 256 == self.buf[4 + ln]:
                out.append((self.buf[1], typ, data))
                del self.buf[:5 + ln]
            else:
                del self.buf[:1]
        return out


def f32(d, o):
    return struct.unpack_from("<f", d, o)[0]


def clean(x):
    """JSON'a NaN/inf yazılmasın."""
    if isinstance(x, float) and not math.isfinite(x):
        return None
    if isinstance(x, dict):
        return {k: clean(v) for k, v in x.items()}
    return x


# ---------------------------------------------------------------- kayıt deposu
class Store:
    def __init__(self, path):
        self.path = path
        self.lock = threading.Lock()
        self.data = array("d")
        if os.path.exists(path):
            raw = open(path, "rb").read()
            raw = raw[:len(raw) // (ROW * 8) * ROW * 8]
            self.data.frombytes(raw)
        self.times = list(self.data[0::ROW])
        self.f = open(path, "ab")
        self.last_flush = time.time()

    @property
    def n(self):
        return len(self.times)

    def append(self, row):
        with self.lock:
            a = array("d", row)
            self.data.extend(a)
            self.times.append(row[0])
            self.f.write(a.tobytes())
            if time.time() - self.last_flush > 5:
                self.f.flush()
                self.last_flush = time.time()

    def since(self, t):
        with self.lock:
            k = bisect.bisect_right(self.times, t)
            return self.data[k * ROW:].tobytes()

    def info(self):
        with self.lock:
            return {"n": self.n, "first": self.times[0] if self.times else None,
                    "last": self.times[-1] if self.times else None}

    def clear(self):
        with self.lock:
            self.f.close()
            if self.times:
                arch = os.path.join(os.path.dirname(self.path), "arsiv")
                os.makedirs(arch, exist_ok=True)
                stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(self.times[0]))
                os.replace(self.path, os.path.join(arch, f"dps150_kayit_{stamp}.bin"))
            self.data = array("d")
            self.times = []
            self.f = open(self.path, "ab")

    def close(self):
        with self.lock:
            self.f.flush()
            self.f.close()


# ---------------------------------------------------------------- merkez
class Hub:
    def __init__(self, store, hwflow):
        self.store = store
        self.tests_path = os.path.splitext(store.path)[0] + "_testler.json"
        self.tests = self.load_tests()
        self.hwflow = hwflow
        self.lock = threading.Lock()
        self.clients = []
        self.device = None
        self.recording = False
        self.rec_start = None
        self.duration = 0
        self.port = None
        self.connected = False
        self.error = ""
        self.frames = 0
        self.st = {"vin": None, "temp": None, "mode": -1, "prot": 0, "out_on": None,
                   "info": {}, "settings": None}

    def load_tests(self):
        try:
            v = json.load(open(self.tests_path, encoding="utf-8"))
            if isinstance(v, list) and v:
                return v
        except (OSError, ValueError):
            pass
        return [{"start": 0, "note": ""}]

    def set_tests(self, tests):
        if not isinstance(tests, list) or not tests:
            raise RuntimeError("Geçersiz test listesi.")
        clean_list = []
        for x in tests[:500]:
            clean_list.append({"start": float(x.get("start", 0)), "note": str(x.get("note", ""))[:300]})
        clean_list.sort(key=lambda x: x["start"])
        self.tests = clean_list
        tmp = self.tests_path + ".tmp"
        json.dump(self.tests, open(tmp, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
        os.replace(tmp, self.tests_path)

    def state(self):
        s = {"server": True, "recording": self.recording, "rec_start": self.rec_start,
             "duration": self.duration, "port": self.port, "connected": self.connected,
             "error": self.error, "frames": self.frames, "hwflow": self.hwflow, "st": self.st,
             "tests": self.tests}
        s.update(self.store.info())
        return clean(s)

    def broadcast(self, event, data):
        msg = f"event: {event}\ndata: {data}\n\n".encode()
        with self.lock:
            for q in list(self.clients):
                try:
                    q.put_nowait(msg)
                except queue.Full:
                    pass

    def start(self, port, duration=0, hwflow=None):
        if self.recording:
            raise RuntimeError("Kayıt zaten sürüyor.")
        if hwflow is not None:
            self.hwflow = bool(hwflow)
        self.port = port
        self.duration = float(duration or 0)
        self.recording = True
        self.rec_start = time.time()
        self.error = ""
        self.frames = 0
        self.device = Device(self, port, self.hwflow)
        self.device.start()

    def stop(self):
        self.recording = False
        if self.device:
            self.device.stop()
            self.device = None
        self.connected = False
        self.store.f.flush()

    def write(self, pkt):
        if not self.device or not self.connected:
            raise RuntimeError("Cihaz bağlı değil.")
        self.device.write(pkt)


class Device(threading.Thread):
    def __init__(self, hub, port, hwflow):
        super().__init__(daemon=True)
        self.hub, self.port, self.hwflow = hub, port, hwflow
        self.ser = None
        self.alive = True
        self.wlock = threading.Lock()
        self.last_frame = 0.0

    def write(self, pkt):
        with self.wlock:
            if self.ser:
                self.ser.write(pkt)
                time.sleep(0.05)

    def stop(self):
        self.alive = False
        try:
            self.write(make_packet(CMD_SESSION, 0, 0))  # oturumu kapat, cihaz tuşları açılsın
        except Exception:
            pass
        try:
            if self.ser:
                self.ser.close()
        except Exception:
            pass

    def run(self):
        import serial
        hub = self.hub
        while self.alive:
            try:
                self.ser = serial.Serial(self.port, 115200, timeout=0.1, rtscts=self.hwflow)
                time.sleep(0.3)
                self.ser.reset_input_buffer()
                hub.connected, hub.error = True, ""
                self.write(make_packet(CMD_SESSION, 0, 1))
                self.write(make_packet(CMD_BAUD, 0, BAUDS.index(115200) + 1))
                for t in (T_MODEL, T_HW, T_FW):
                    self.write(make_packet(CMD_GET, t, 0))
                self.write(make_packet(CMD_GET, T_ALL, 0))
                self.loop()
            except Exception as e:
                if self.alive:
                    hub.connected = False
                    hub.error = f"{type(e).__name__}: {e}"
                    print(f"\n[seri] {hub.error} — 3 sn sonra yeniden denenecek")
            finally:
                try:
                    if self.ser:
                        self.ser.close()
                except Exception:
                    pass
                self.ser = None
            if self.alive:
                time.sleep(3)

    def loop(self):
        hub, st = self.hub, self.hub.st
        parser = FrameParser()
        last_poll = last_all = time.time()
        last_t = 0.0
        while self.alive:
            now = time.time()
            if now - self.last_frame > 0.5 and now - last_poll > 0.5:
                self.write(make_packet(CMD_GET, T_ALL, 0))
                last_poll = last_all = now
            elif now - last_all > 10:
                self.write(make_packet(CMD_GET, T_ALL, 0))
                last_all = now
            chunk = self.ser.read(512)
            if not chunk:
                continue
            for cmd, typ, d in parser.feed(chunk):
                hub.frames += 1
                sample = None
                if typ == T_VIN and len(d) >= 4:
                    st["vin"] = f32(d, 0)
                elif typ == T_TEMP and len(d) >= 4:
                    st["temp"] = f32(d, 0)
                elif typ == T_MODE and d:
                    st["mode"] = 0 if d[0] == 0 else 1
                elif typ == T_PROT and d:
                    st["prot"] = d[0]
                elif typ == T_OUT_ON and d:
                    st["out_on"] = d[0] == 1
                elif typ in (T_MODEL, T_HW, T_FW):
                    key = {T_MODEL: "model", T_HW: "hw", T_FW: "fw"}[typ]
                    st["info"][key] = d.decode("ascii", "replace").strip("\x00 ")
                elif typ == T_OUT and len(d) >= 12:
                    sample = (f32(d, 0), f32(d, 4), f32(d, 8))
                elif typ == T_ALL and len(d) >= 110:
                    st["vin"], st["temp"] = f32(d, 0), f32(d, 24)
                    st["out_on"], st["prot"] = d[107] == 1, d[108]
                    st["mode"] = 0 if d[109] == 0 else 1
                    st["settings"] = {"vset": f32(d, 4), "iset": f32(d, 8),
                                      "ovp": f32(d, 76), "ocp": f32(d, 80)}
                    sample = (f32(d, 12), f32(d, 16), f32(d, 20))
                if sample:
                    t = time.time()
                    if t - last_t < 0.01:
                        continue
                    last_t = self.last_frame = t
                    vin = st["vin"] if st["vin"] is not None else float("nan")
                    tmp = st["temp"] if st["temp"] is not None else float("nan")
                    row = [t, sample[0], sample[1], sample[2], vin, tmp, float(st["mode"]), float(st["prot"])]
                    hub.store.append(row)
                    hub.broadcast("s", ",".join(repr(x) for x in row))


# ---------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    hub = None
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass

    def send_json(self, obj, code=200):
        b = json.dumps(obj, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(b)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(b)

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        if not n:
            return {}
        try:
            return json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            return {}

    def do_GET(self):
        u = urlparse(self.path)
        hub = self.hub
        if u.path in ("/", "/index.html"):
            try:
                b = open(os.path.join(HERE, "index.html"), "rb").read()
            except OSError:
                return self.send_json({"error": "index.html bu klasörde bulunamadı"}, 404)
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(b)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(b)
        elif u.path == "/api/info":
            self.send_json(hub.state())
        elif u.path == "/api/ports":
            try:
                from serial.tools import list_ports
                ports = [{"device": p.device, "description": p.description or "", "hwid": p.hwid or ""}
                         for p in list_ports.comports()]
            except Exception as e:
                return self.send_json({"error": str(e)}, 500)
            self.send_json({"ports": ports})
        elif u.path == "/api/history":
            since = float(parse_qs(u.query).get("since", ["0"])[0] or 0)
            b = hub.store.since(since)
            self.send_response(200)
            self.send_header("Content-Type", "application/octet-stream")
            self.send_header("Content-Length", str(len(b)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(b)
        elif u.path == "/api/stream":
            self.stream()
        else:
            self.send_json({"error": "bulunamadı"}, 404)

    def stream(self):
        hub = self.hub
        q = queue.Queue(maxsize=20000)
        with hub.lock:
            hub.clients.append(q)
        try:
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "keep-alive")
            self.end_headers()
            self.close_connection = True
            self.wfile.write(f"event: state\ndata: {json.dumps(hub.state())}\n\n".encode())
            self.wfile.flush()
            while True:
                try:
                    msg = q.get(timeout=15)
                except queue.Empty:
                    msg = b": ping\n\n"
                self.wfile.write(msg)
                self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            pass
        finally:
            with hub.lock:
                if q in hub.clients:
                    hub.clients.remove(q)

    def do_POST(self):
        u = urlparse(self.path)
        hub = self.hub
        b = self.body()
        try:
            if u.path == "/api/start":
                if not b.get("port"):
                    raise RuntimeError("Port seçilmedi.")
                hub.start(b["port"], b.get("duration", 0), b.get("hwflow"))
                print(f"\n[kayıt] başladı: {b['port']}")
            elif u.path == "/api/stop":
                hub.stop()
                print("\n[kayıt] durduruldu")
            elif u.path == "/api/raw":
                pkt = bytes.fromhex(b.get("hex", ""))
                if len(pkt) < 5 or pkt[0] != HDR_TX:
                    raise RuntimeError("Geçersiz paket.")
                hub.write(pkt)
            elif u.path == "/api/tests":
                hub.set_tests(b.get("tests"))
            elif u.path == "/api/tests/new":
                hub.set_tests(hub.tests + [{"start": time.time(), "note": str(b.get("note", ""))}])
                print(f"\n[test] yeni test başladı: {len(hub.tests)}")
            elif u.path == "/api/clear":
                if hub.recording:
                    raise RuntimeError("Kayıt sürerken silinemez. Önce durdurun.")
                if hub.store.times and os.path.exists(hub.tests_path):
                    arch = os.path.join(os.path.dirname(hub.store.path), "arsiv")
                    os.makedirs(arch, exist_ok=True)
                    stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(hub.store.times[0]))
                    os.replace(hub.tests_path, os.path.join(arch, f"dps150_kayit_{stamp}_testler.json"))
                hub.tests = [{"start": 0, "note": ""}]
                hub.store.clear()
                print("\n[kayıt] silindi (arsiv/ klasörüne taşındı)")
            else:
                return self.send_json({"error": "bulunamadı"}, 404)
            hub.broadcast("state", json.dumps(hub.state()))
            self.send_json(hub.state())
        except Exception as e:
            self.send_json({"error": str(e)}, 400)


# ---------------------------------------------------------------- yardımcılar
def lan_ips():
    ips = set()
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ips.add(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    try:
        for ip in socket.gethostbyname_ex(socket.gethostname())[2]:
            if not ip.startswith("127."):
                ips.add(ip)
    except OSError:
        pass
    return sorted(ips)


PAGE_URL = "https://hrn190.github.io/dps150/"


def update_page():
    """Sayfanın en güncel halini GitHub Pages'ten indir; olmazsa yerel kopya kullanılır."""
    dst = os.path.join(HERE, "index.html")
    try:
        from urllib.request import urlopen
        b = urlopen(PAGE_URL, timeout=6).read()
        if b"DPS-150" in b and b"api/info" in b:
            old = open(dst, "rb").read() if os.path.exists(dst) else b""
            if b != old:
                open(dst, "wb").write(b)
                print("Sayfa GitHub'dan güncellendi.")
            return
    except Exception as e:
        print(f"Sayfa GitHub'dan alınamadı ({type(e).__name__}); yerel kopya kullanılacak.")
    if not os.path.exists(dst):
        print("UYARI: index.html bulunamadı; sayfa açılmayacak. index.html'i bu klasöre koyun.")


def ticker(hub):
    while True:
        time.sleep(1)
        if hub.recording and hub.duration and time.time() - hub.rec_start >= hub.duration:
            hub.stop()
            print("\n[kayıt] süre doldu")
        hub.broadcast("state", json.dumps(hub.state()))
        if hub.recording:
            i = hub.store.info()
            el = time.time() - hub.rec_start
            sys.stdout.write(f"\r[kayıt] {int(el // 3600):02d}:{int(el % 3600 // 60):02d}:{int(el % 60):02d}  "
                             f"{'bağlı' if hub.connected else 'bağlantı bekleniyor'}  örnek={i['n']}  "
                             f"izleyen={len(hub.clients)}     ")
            sys.stdout.flush()


def main():
    ap = argparse.ArgumentParser(description="DPS-150 LAN sunucusu")
    ap.add_argument("--http-port", type=int, default=8150)
    ap.add_argument("--port", help="seri port, ör. COM7 (--baslat ile birlikte)")
    ap.add_argument("--baslat", action="store_true", help="sunucu açılınca kayda başla")
    ap.add_argument("--no-rtscts", action="store_true", help="donanım akış kontrolünü kapat")
    ap.add_argument("--guncelleme-yok", action="store_true", help="sayfayı GitHub'dan güncelleme")
    ap.add_argument("--veri", default=os.path.join(HERE, "dps150_kayit.bin"), help="kayıt dosyası")
    args = ap.parse_args()

    try:
        import serial  # noqa: F401
    except ImportError:
        sys.exit("pyserial yüklü değil:  pip install pyserial")

    if not args.guncelleme_yok:
        update_page()
    store = Store(args.veri)
    hub = Hub(store, hwflow=not args.no_rtscts)
    Handler.hub = hub
    if args.baslat:
        if not args.port:
            sys.exit("--baslat için --port gerekli (ör. --port COM7)")
        hub.start(args.port)
    threading.Thread(target=ticker, args=(hub,), daemon=True).start()

    srv = ThreadingHTTPServer(("0.0.0.0", args.http_port), Handler)
    srv.daemon_threads = True
    print("DPS-150 sunucusu çalışıyor. Aynı ağdan şu adreslerle bağlanın:")
    for ip in lan_ips() or ["<bu-bilgisayarın-ip-adresi>"]:
        print(f"   http://{ip}:{args.http_port}")
    print(f"   (bu bilgisayardan: http://localhost:{args.http_port})")
    print(f"Kayıt dosyası: {args.veri}  ({store.n} örnek)")
    print("Kapatmak için Ctrl+C. Kayıt sürüyorsa bu pencere açık kalmalı.\n")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nKapatılıyor…")
    finally:
        hub.stop()
        store.close()


if __name__ == "__main__":
    main()
