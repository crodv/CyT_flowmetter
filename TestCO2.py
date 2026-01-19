# -*- coding: utf-8 -*-
"""
Ventana única para probar el caudalímetro de CO2 (ADS1115).
"""

import os
import csv
import random
import math
import time
import datetime as dt
from importlib import util as importlib_util

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

_ADS_I2C = None

# ===== MODO SIMULADOR =====
SIMULADOR = os.environ.get("SIMULADOR", "").strip().lower() in {"1", "true", "yes"}

# ===== Configuracion caudalimetro CO2 (ADS1115) =====

def parse_int(value: str, default: int) -> int:
    raw = (value or "").strip().lower()
    if not raw:
        return default
    if raw.startswith("0x"):
        return int(raw, 16)
    return int(raw, 10)


ADS1115_ADDR = parse_int(os.environ.get("ADS1115_ADDR", "0x48"), 0x48)
ADS1115_CH = parse_int(os.environ.get("ADS1115_CH", "1"), 1)
ADS1115_GAIN = parse_int(os.environ.get("ADS1115_GAIN", "1"), 1)

SHUNT_OHMS = float(os.environ.get("SHUNT_OHMS", "147.0"))
FLOW_MIN_SCCM = float(os.environ.get("FLOW_MIN_SCCM", os.environ.get("FLOW_MIN_M3H", "0.0")))
FLOW_MAX_SCCM = float(os.environ.get("FLOW_MAX_SCCM", os.environ.get("FLOW_MAX_M3H", "50.0")))
CO2_DENSITY_G_M3 = float(os.environ.get("CO2_DENSITY_G_M3", "1964.0"))
BROTH_VOLUME_L = float(os.environ.get("BROTH_VOLUME_L", "5.0"))

SAMPLE_PERIOD_SEC_ENV = os.environ.get("SAMPLE_PERIOD_SEC", "").strip()
SAMPLE_PERIOD_SEC = parse_int(SAMPLE_PERIOD_SEC_ENV, 0) if SAMPLE_PERIOD_SEC_ENV else None
PLOT_WINDOW_ENV = os.environ.get("PLOT_WINDOW_HOURS", "").strip()
PLOT_WINDOW_HOURS = float(PLOT_WINDOW_ENV) if PLOT_WINDOW_ENV else 0.0
MAX_FLOW_HISTORY_HOURS = 24 * 21

FERMENTER_NAME = os.environ.get("CO2_NAME", "F1").strip() or "F1"


# ===== Utilidades =====

def now():
    return dt.datetime.now()


def _restore_focus(widget):
    try:
        root = widget.winfo_toplevel()
        root.focus_force()
        root.update_idletasks()
        root.after(10, root.focus_force)
    except Exception:
        pass


def voltage_to_current_ma(voltage: float, shunt_ohms: float) -> float:
    return (voltage / shunt_ohms) * 1000.0


def current_to_flow_sccm(current_ma: float) -> float:
    if FLOW_MAX_SCCM <= FLOW_MIN_SCCM:
        return 0.0
    current_ma = max(4.0, min(20.0, current_ma))
    span = 16.0
    return FLOW_MIN_SCCM + (current_ma - 4.0) * (FLOW_MAX_SCCM - FLOW_MIN_SCCM) / span


def flow_to_rate_g_l_h(flow_sccm: float) -> float:
    if CO2_DENSITY_G_M3 <= 0 or BROTH_VOLUME_L <= 0:
        return 0.0
    flow_m3h = flow_sccm * 6e-5
    return (flow_m3h * CO2_DENSITY_G_M3) / BROTH_VOLUME_L


# ===== ADS1115 / Caudalimetro CO2 =====
class ADS1115Reader:
    def __init__(self, address: int, channel: int, gain: int):
        self.address = address
        self.channel = max(0, min(3, channel))
        self.gain = gain
        self.sim = SIMULADOR
        self.sim_reason = ""
        self._sim_start = time.monotonic()
        self._ads = None
        self._chan = None
        self._init_hw()

    def _init_hw(self):
        global _ADS_I2C
        if self.sim:
            self.sim_reason = "Forzado por variable de entorno"
            return
        try:
            import board  # type: ignore
            import busio  # type: ignore
            import adafruit_ads1x15.ads1115 as ADS  # type: ignore
            from adafruit_ads1x15.analog_in import AnalogIn  # type: ignore
        except Exception as exc:
            self.sim = True
            self.sim_reason = f"Fallback a simulador: {exc}"
            return

        try:
            if _ADS_I2C is None:
                _ADS_I2C = busio.I2C(board.SCL, board.SDA)
            i2c = _ADS_I2C
            ads = ADS.ADS1115(i2c, address=self.address)
            ads.gain = self.gain
            try:
                ch_map = [ADS.P0, ADS.P1, ADS.P2, ADS.P3]
            except AttributeError:
                try:
                    from adafruit_ads1x15.ads1x15 import Pin  # type: ignore
                    ch_map = [Pin.A0, Pin.A1, Pin.A2, Pin.A3]
                except Exception:
                    ch_map = [0, 1, 2, 3]
            self._ads = ads
            self._chan = AnalogIn(ads, ch_map[self.channel])
        except Exception as exc:
            self.sim = True
            self.sim_reason = f"Fallback a simulador: {exc}"
            self._ads = None
            self._chan = None

    def read_voltage(self) -> float:
        if self.sim or not self._chan:
            t_hours = (time.monotonic() - self._sim_start) / 3600.0
            tr = 0.2
            td = 4.0
            if td <= tr:
                td = tr + 0.1
            t_peak = (tr * td / (td - tr)) * math.log(td / tr)
            peak_shape = math.exp(-t_peak / td) - math.exp(-t_peak / tr)
            peak_shape = peak_shape if peak_shape > 0 else 1.0
            amplitude = FLOW_MAX_SCCM / peak_shape
            flow_sccm = amplitude * (math.exp(-t_hours / td) - math.exp(-t_hours / tr))
            flow_sccm += random.uniform(-0.3, 0.3)
            flow_sccm = max(FLOW_MIN_SCCM, min(FLOW_MAX_SCCM, flow_sccm))
            if FLOW_MAX_SCCM > FLOW_MIN_SCCM:
                current_ma = 4.0 + (flow_sccm - FLOW_MIN_SCCM) * 16.0 / (FLOW_MAX_SCCM - FLOW_MIN_SCCM)
            else:
                current_ma = 4.0
            current_ma = max(4.0, min(20.0, current_ma))
            return (current_ma / 1000.0) * SHUNT_OHMS
        return float(self._chan.voltage)

    def close(self):
        global _ADS_I2C
        self._chan = None
        self._ads = None
        if _ADS_I2C is not None:
            try:
                _ADS_I2C.deinit()
            except Exception:
                pass
            _ADS_I2C = None


# ===== LED widget =====
class Led:
    def __init__(self, parent, size=20):
        bg = None
        for key in ("fg_color", "background", "bg"):
            try:
                bg = parent.cget(key)
                break
            except Exception:
                continue
        if bg is None:
            bg = "#111827"
        self.canvas = tk.Canvas(
            parent,
            width=size,
            height=size,
            highlightthickness=0,
            bd=0,
            bg=bg,
        )
        r = 2
        self.oval = self.canvas.create_oval(r, r, size - r, size - r, fill="red", outline="#111")

    def widget(self):
        return self.canvas

    def set_color(self, color: str):
        self.canvas.itemconfig(self.oval, fill=color)


# ===== App CO2 =====
class CO2App(tk.Tk):
    def __init__(self, fermenter_name: str):
        super().__init__()
        self.fermenter = fermenter_name

        self.title(f"Caudal CO2 en tiempo real – {self.fermenter}")
        self.minsize(900, 700)

        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            raise SystemExit(1)

        self.flow_readers = {}
        self.flow_samples = {}
        self.flow_next_sample = {}
        self.flow_sample_period = {}
        self.co2_csv_dir = {}
        self.co2_csv_name = {}
        self.co2_csv_running = {}
        self.co2_csv_paused = {}
        self.co2_csv_last_export_ok = {}
        self._co2_csv_leds = {}

        addr_env = os.environ.get(f"ADS1115_ADDR_{self.fermenter}", "").strip()
        ch_env = os.environ.get(f"ADS1115_CH_{self.fermenter}", "").strip()
        gain_env = os.environ.get(f"ADS1115_GAIN_{self.fermenter}", "").strip()
        addr = parse_int(addr_env, ADS1115_ADDR) if addr_env else ADS1115_ADDR
        ch = parse_int(ch_env, ADS1115_CH) if ch_env else ADS1115_CH
        gain = parse_int(gain_env, ADS1115_GAIN) if gain_env else ADS1115_GAIN
        reader = ADS1115Reader(addr, ch, gain)
        self.flow_readers[self.fermenter] = reader
        self.flow_samples[self.fermenter] = []
        self.flow_next_sample[self.fermenter] = None
        if SAMPLE_PERIOD_SEC is None:
            period = 1 if reader.sim else 10
        else:
            period = SAMPLE_PERIOD_SEC
        self.flow_sample_period[self.fermenter] = period

        self.co2_csv_dir[self.fermenter] = tk.StringVar(value=os.path.abspath("./Proceso"))
        self.co2_csv_name[self.fermenter] = tk.StringVar(value=f"{self.fermenter}_co2.csv")
        self.co2_csv_running[self.fermenter] = False
        self.co2_csv_paused[self.fermenter] = False
        self.co2_csv_last_export_ok[self.fermenter] = False
        os.makedirs(self.co2_csv_dir[self.fermenter].get(), exist_ok=True)

        self._refresh_job = None
        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.refresh()

    # ===== CSV CO2 =====
    def _co2_csv_path(self, fermenter):
        name = self.co2_csv_name[fermenter].get().strip() or f"{fermenter}_co2.csv"
        if not name.lower().endswith(".csv"):
            name += ".csv"
        return os.path.join(self.co2_csv_dir[fermenter].get(), name)

    def _co2_csv_state_led(self, fermenter, color):
        led = self._co2_csv_leds.get(fermenter)
        if led is not None:
            led.set_color(color)

    def co2_pick_dir(self, fermenter):
        d = filedialog.askdirectory(title="Elegir carpeta de trabajo CSV CO2")
        _restore_focus(self)
        if d:
            self.co2_csv_dir[fermenter].set(d)
            os.makedirs(d, exist_ok=True)

    def co2_csv_start(self, fermenter):
        self.co2_csv_running[fermenter] = True
        self.co2_csv_paused[fermenter] = False
        self.co2_csv_last_export_ok[fermenter] = False
        self._co2_csv_state_led(fermenter, "#22c55e")

    def co2_csv_pause(self, fermenter):
        self.co2_csv_running[fermenter] = False
        self.co2_csv_paused[fermenter] = True
        self._co2_csv_state_led(fermenter, "#eab308")

    def co2_csv_export(self, fermenter):
        if self.co2_csv_running[fermenter]:
            messagebox.showerror("Exportar", "Detén o pausa el CSV antes de exportar.")
            return
        src = self._co2_csv_path(fermenter)
        if not os.path.exists(src):
            messagebox.showerror("Exportar", f"No existe {src}")
            return
        dst_dir = filedialog.askdirectory(title="Seleccionar carpeta de destino")
        _restore_focus(self)
        if not dst_dir:
            return
        try:
            dst = os.path.join(dst_dir, os.path.basename(src))
            with open(src, "r", encoding="utf-8") as fsrc, open(dst, "w", encoding="utf-8", newline="") as fdst:
                fdst.write(fsrc.read())
            self.co2_csv_last_export_ok[fermenter] = True
            self._co2_csv_state_led(fermenter, "#3b82f6")
            messagebox.showinfo("Exportar", f"Archivo exportado a:\n{dst}")
        except Exception as e:
            messagebox.showerror("Exportar", f"No se pudo exportar.\n{e}")

    def co2_csv_restart(self, fermenter):
        self.co2_csv_running[fermenter] = False
        self.co2_csv_paused[fermenter] = False
        path = self._co2_csv_path(fermenter)
        try:
            if os.path.exists(path):
                os.remove(path)
            self._co2_csv_state_led(fermenter, "#ef4444")
            messagebox.showinfo("CSV CO2", f"Archivo reiniciado:\n{path}")
        except Exception as e:
            messagebox.showerror("CSV CO2", f"No se pudo reiniciar.\n{e}")

    def _co2_csv_write_row(self, fermenter, ts, flow, current_ma, voltage, status):
        if not self.co2_csv_running.get(fermenter, False):
            return
        row = {
            "timestamp": ts.strftime("%Y-%m-%d %H:%M:%S"),
            "fermentador": fermenter,
            "flow_sccm": f"{flow:.4f}",
            "rate_g_l_h": f"{flow_to_rate_g_l_h(flow):.6f}",
            "current_ma": f"{current_ma:.3f}",
            "voltage_v": f"{voltage:.4f}",
            "status": status,
        }
        ipath = self._co2_csv_path(fermenter)
        header = not os.path.exists(ipath)
        try:
            os.makedirs(os.path.dirname(ipath), exist_ok=True)
            with open(ipath, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("CSV CO2", f"No se pudo escribir en {ipath}\n{e}")

    # ===== Flow sampling =====
    def _flow_take_sample(self, fermenter, ts=None):
        reader = self.flow_readers.get(fermenter)
        if reader is None:
            return
        if ts is None:
            ts = now()
        try:
            voltage = reader.read_voltage()
        except Exception as exc:
            print(f"[FLOW] Error leyendo {fermenter}: {exc}")
            next_ts = ts + dt.timedelta(seconds=self.flow_sample_period[fermenter])
            self.flow_next_sample[fermenter] = next_ts
            return

        current_ma = voltage_to_current_ma(voltage, SHUNT_OHMS)
        flow = current_to_flow_sccm(current_ma)
        status = "OK"
        if current_ma < 3.8:
            status = "Bajo rango"
        elif current_ma > 20.5:
            status = "Alto rango"

        samples = self.flow_samples.get(fermenter, [])
        samples.append((ts, flow, current_ma, voltage, status))
        cutoff = ts - dt.timedelta(hours=MAX_FLOW_HISTORY_HOURS)
        self.flow_samples[fermenter] = [row for row in samples if row[0] >= cutoff]
        self._co2_csv_write_row(fermenter, ts, flow, current_ma, voltage, status)
        self.flow_next_sample[fermenter] = ts + dt.timedelta(seconds=self.flow_sample_period[fermenter])

    def _flow_tick(self):
        ts = now()
        for name in self.flow_readers:
            next_ts = self.flow_next_sample.get(name)
            if next_ts is None or ts >= next_ts:
                self._flow_take_sample(name, ts=ts)

    # ===== UI =====
    def _build_ui(self):
        reader = self.flow_readers[self.fermenter]

        header = ttk.Frame(self)
        header.pack(fill="x", padx=8, pady=(8, 4))
        ttk.Label(header, text="Caudalímetro CO2 (4-20 mA)", font=("Segoe UI", 14, "bold")).pack(side="left")
        mode_text = "SIMULADOR" if reader.sim else "HARDWARE"
        mode_color = "#dc2626" if reader.sim else "#16a34a"
        mode_box = ttk.Frame(header)
        mode_box.pack(side="right")
        ttk.Label(mode_box, text=mode_text, foreground=mode_color).pack(side="top", anchor="e")
        if reader.sim and reader.sim_reason:
            ttk.Label(mode_box, text=reader.sim_reason, foreground="#6b7280").pack(side="top", anchor="e")

        stats = ttk.Frame(self)
        stats.pack(fill="x", padx=8, pady=(0, 6))
        stats.grid_columnconfigure(1, weight=1)

        self.flow_var = tk.StringVar(value="0.00 SCCM")
        self.rate_var = tk.StringVar(value="0.0000 g/L*h")
        self.current_var = tk.StringVar(value="0.00 mA")
        self.voltage_var = tk.StringVar(value="0.000 V")
        self.status_var = tk.StringVar(value="Esperando...")
        self.next_var = tk.StringVar(value="--:--:--")

        ttk.Label(stats, text="Caudal:", font=("Segoe UI", 12, "bold")).grid(row=0, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.flow_var, font=("Segoe UI", 12)).grid(row=0, column=1, sticky="w")
        ttk.Label(stats, text="Tasa fermentación:", font=("Segoe UI", 12, "bold")).grid(row=1, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.rate_var, font=("Segoe UI", 12)).grid(row=1, column=1, sticky="w")
        ttk.Label(stats, text="Corriente:", font=("Segoe UI", 12, "bold")).grid(row=2, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.current_var, font=("Segoe UI", 12)).grid(row=2, column=1, sticky="w")
        ttk.Label(stats, text="Voltaje:", font=("Segoe UI", 12, "bold")).grid(row=3, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.voltage_var, font=("Segoe UI", 12)).grid(row=3, column=1, sticky="w")
        ttk.Label(stats, text="Estado:", font=("Segoe UI", 12, "bold")).grid(row=4, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.status_var, font=("Segoe UI", 12)).grid(row=4, column=1, sticky="w")
        ttk.Label(stats, text="Siguiente muestra:", font=("Segoe UI", 12, "bold")).grid(row=5, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.next_var, font=("Segoe UI", 12)).grid(row=5, column=1, sticky="w")
        ttk.Label(stats, text="SCCM = cm3/min", font=("Segoe UI", 10, "italic")).grid(
            row=6, column=0, columnspan=2, sticky="w", pady=(4, 0)
        )

        control = ttk.Frame(self)
        control.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(control, text="Escala:").pack(side="left")

        self.current_window_hours = PLOT_WINDOW_HOURS if PLOT_WINDOW_HOURS > 0 else None

        def set_window(h):
            self.current_window_hours = h
            self._update_plot()

        for label, hours in [
            ("1 h", 1),
            ("12 h", 12),
            ("24 h", 24),
            ("48 h", 48),
            ("72 h", 72),
            ("1 semana", 24 * 7),
            ("2 semanas", 24 * 14),
            ("3 semanas", 24 * 21),
        ]:
            ttk.Button(control, text=label, command=lambda h=hours: set_window(h)).pack(side="left", padx=2)

        csv_box = ttk.Frame(self)
        csv_box.pack(fill="x", padx=8, pady=(0, 6))
        csv_box.grid_columnconfigure(1, weight=1)

        ttk.Label(csv_box, text="CSV CO2", font=("Segoe UI", 12, "bold")).grid(
            row=0, column=0, columnspan=3, sticky="w"
        )

        ttk.Label(csv_box, text="Carpeta:").grid(row=1, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(csv_box, textvariable=self.co2_csv_dir[self.fermenter]).grid(
            row=1, column=1, sticky="ew", pady=2
        )
        ttk.Button(csv_box, text="...", width=4, command=lambda: self.co2_pick_dir(self.fermenter)).grid(
            row=1, column=2, sticky="w", pady=2
        )

        ttk.Label(csv_box, text="Archivo:").grid(row=2, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(csv_box, textvariable=self.co2_csv_name[self.fermenter]).grid(
            row=2, column=1, sticky="ew", pady=2
        )

        btn_row = ttk.Frame(csv_box)
        btn_row.grid(row=3, column=0, columnspan=3, sticky="ew", pady=(6, 4))
        for i in range(4):
            btn_row.grid_columnconfigure(i, weight=1)

        ttk.Button(btn_row, text="Inicio/Reanudar", command=lambda: self.co2_csv_start(self.fermenter)).grid(
            row=0, column=0, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Pausar/Detener", command=lambda: self.co2_csv_pause(self.fermenter)).grid(
            row=0, column=1, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Exportar CSV", command=lambda: self.co2_csv_export(self.fermenter)).grid(
            row=0, column=2, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Borrar/Reiniciar", command=lambda: self.co2_csv_restart(self.fermenter)).grid(
            row=0, column=3, padx=2, sticky="ew"
        )

        state_row = ttk.Frame(csv_box)
        state_row.grid(row=4, column=0, columnspan=3, sticky="ew", pady=(2, 0))
        ttk.Label(state_row, text="Estado:").pack(side="left")
        led = Led(state_row)
        led.widget().pack(side="left", padx=6)
        self._co2_csv_leds[self.fermenter] = led
        led.set_color("#ef4444")

        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore

        self.fig, (self.ax_flow, self.ax_rate) = plt.subplots(
            2,
            1,
            sharex=True,
            figsize=(9, 6),
            gridspec_kw={"height_ratios": [3, 2], "hspace": 0.2},
        )
        self.line_flow, = self.ax_flow.plot([], [], color="#2563eb", linewidth=2, label="Caudal")
        self.line_rate, = self.ax_rate.plot([], [], color="#f97316", linewidth=2, linestyle="--", label="dCO2/dt")
        self.ax_flow.set_title("Caudal CO2 (SCCM)")
        self.ax_flow.set_ylabel("SCCM")
        self.ax_flow.grid(True, alpha=0.2)
        self.ax_rate.set_title("Tasa de fermentación (dCO2/dt)")
        self.ax_rate.set_ylabel("g/L*h")
        self.ax_rate.set_xlabel("Hora")
        self.ax_rate.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M"))
        self.ax_rate.grid(True, alpha=0.2)

        canvas = FigureCanvasTkAgg(self.fig, master=self)
        canvas.get_tk_widget().pack(fill="both", expand=True)
        self.canvas = canvas

    def _windowed_samples(self, samples):
        if not samples:
            return []
        if self.current_window_hours is None:
            return samples
        right = samples[-1][0]
        left = right - dt.timedelta(hours=self.current_window_hours)
        return [row for row in samples if row[0] >= left]

    def _update_plot(self):
        samples = self.flow_samples.get(self.fermenter, [])
        windowed = self._windowed_samples(samples)
        if not windowed:
            return
        times = [ts for ts, _, _, _, _ in windowed]
        values = [flow for _, flow, _, _, _ in windowed]
        self.line_flow.set_data(times, values)
        rate_values = [flow_to_rate_g_l_h(flow) for flow in values]
        self.line_rate.set_data(times, rate_values)

        right = times[-1]
        if self.current_window_hours is None:
            left = times[0]
            if left == right:
                left = right - dt.timedelta(seconds=max(1, self.flow_sample_period[self.fermenter]))
        else:
            left = right - dt.timedelta(hours=self.current_window_hours)
        self.ax_flow.set_xlim(left, right)

        vmin = min(values)
        vmax = max(values)
        pad = (vmax - vmin) * 0.1 if vmax != vmin else 1.0
        self.ax_flow.set_ylim(vmin - pad, vmax + pad)
        rmin = min(rate_values)
        rmax = max(rate_values)
        rpad = (rmax - rmin) * 0.1 if rmax != rmin else 1.0
        self.ax_rate.set_ylim(rmin - rpad, rmax + rpad)
        self.fig.autofmt_xdate()
        self.canvas.draw_idle()

    def _update_stats(self):
        samples = self.flow_samples.get(self.fermenter, [])
        if not samples:
            self.flow_var.set("0.00 SCCM")
            self.rate_var.set("0.0000 g/L*h")
            self.current_var.set("0.00 mA")
            self.voltage_var.set("0.000 V")
            self.status_var.set("Esperando...")
            return
        _, flow, current_ma, voltage, status = samples[-1]
        self.flow_var.set(f"{flow:0.2f} SCCM")
        self.rate_var.set(f"{flow_to_rate_g_l_h(flow):0.4f} g/L*h")
        self.current_var.set(f"{current_ma:0.2f} mA")
        self.voltage_var.set(f"{voltage:0.3f} V")
        self.status_var.set(status)

    def _update_countdown(self):
        next_sample = self.flow_next_sample.get(self.fermenter)
        if next_sample is None:
            self.next_var.set("--:--:--")
            return
        delta = next_sample - now()
        if delta.total_seconds() < 0:
            self.next_var.set("00:00:00")
        else:
            total = int(delta.total_seconds())
            hh = total // 3600
            mm = (total % 3600) // 60
            ss = total % 60
            self.next_var.set(f"{hh:02d}:{mm:02d}:{ss:02d}")

    def refresh(self):
        self._flow_tick()
        self._update_stats()
        self._update_plot()
        self._update_countdown()
        self._refresh_job = self.after(1000, self.refresh)

    def on_close(self):
        if self._refresh_job is not None:
            try:
                self.after_cancel(self._refresh_job)
            except Exception:
                pass
            self._refresh_job = None
        for reader in self.flow_readers.values():
            try:
                reader.close()
            except Exception:
                pass
        try:
            self.quit()
        except Exception:
            pass
        self.destroy()


if __name__ == "__main__":
    app = CO2App(FERMENTER_NAME)
    app.mainloop()
