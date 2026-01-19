# -*- coding: utf-8 -*-
"""
Codigo hecho por Francisco Rojas para CII Viña concha y toro
Panel de control para 3 fermentadores (Raspberry / Simulador) con interfaz
tipo panel industrial para control de temperatura y nutricion.
"""

import os
import glob
import csv
import random
import math
import time
import datetime as dt
import calendar as pycal
from importlib import util as importlib_util

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import customtkinter as ctk
from PIL import Image  # <<<<<< IMPORT PARA EL LOGO

_ADS_I2C = None

# ===== MODO SIMULADOR =====
SIMULADOR = os.environ.get("SIMULADOR", "").strip().lower() in {"1", "true", "yes"}

ASSETS_DIR = os.path.join(os.path.dirname(__file__), "assets")

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

# ===== PINES HARDWARE =====
RELAY_PINS = {
    "F1": {"cold": 7, "hot": 8},
    "F2": {"cold": 24, "hot": 23},
    "F3": {"cold": 18, "hot": 15},
}
STEPPER_PINS = {
    "F1": {"pul": 13, "dir": 26},
    "F2": {"pul": 21, "dir": 20},
    "F3": {"pul": 12, "dir": 16},
}

# ===== Utilidades de tiempo =====
MESES_ES = [
    "", "Enero", "Febrero", "Marzo", "Abril", "Mayo", "Junio",
    "Julio", "Agosto", "Septiembre", "Octubre", "Noviembre", "Diciembre"
]


def now():
    return dt.datetime.now()


def now_str():
    return now().strftime("%Y-%m-%d %H:%M:%S")


def ymd(date: dt.date) -> str:
    return date.strftime("%Y-%m-%d")


def hhmm_ok(s: str) -> bool:
    try:
        h, m = s.split(":")
        h = int(h)
        m = int(m)
        return 0 <= h <= 23 and 0 <= m <= 59
    except Exception:
        return False


def _normalize_date(date_str: str):
    date_str = (date_str or "").strip()
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%Y/%m/%d"):
        try:
            return dt.datetime.strptime(date_str, fmt).date()
        except Exception:
            continue
    return None


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


# ===== Hardware layer (con fallback simulador) =====
class Hardware:
    def __init__(self):
        self.sim = SIMULADOR
        self.sim_reason = "Forzado por variable de entorno" if self.sim else ""
        self.sim_gpio = self.sim
        self.sim_gpio_reason = "Forzado por variable de entorno" if self.sim else ""
        self.gpio = None
        self.pwms = {}
        self._last_temp_error = False
        self._sim_bias = [random.uniform(-1, 1) for _ in range(3)]
        self.ds_devices = []  # <- aseguramos que exista siempre

        if not self.sim:
            try:
                import RPi.GPIO as GPIO  # type: ignore
                self.gpio = GPIO
                GPIO.setmode(GPIO.BCM)
                GPIO.setwarnings(False)
            except Exception as e:
                # Solo desactivamos GPIO; no afecta ADS1115 ni DS18B20.
                self.sim_gpio = True
                self.sim_gpio_reason = f"GPIO fallback: {e}"
                self.gpio = None

            # Buscamos los DS18B20, pero NO forzamos simulador si no hay
            self.ds_devices = sorted(glob.glob("/sys/bus/w1/devices/28-*"))
            if len(self.ds_devices) < 1:
                print("[HW] Advertencia: no se encontraron DS18B20, "
                      "se usar� 20�C de respaldo para la temperatura.")

        if self.sim:
            print(f"[HW] Modo simulador activo. {self.sim_reason}")
        else:
            if self.sim_gpio:
                print(f"[HW] GPIO en simulador. {self.sim_gpio_reason}")
            else:
                print("[HW] GPIO activo.")
            print("[HW] Modo hardware activo. Sensores detectados:", self.ds_devices)

    def _gpio_fallback(self, exc: Exception):
        if self.sim_gpio:
            return
        self.sim_gpio = True
        self.sim_gpio_reason = f"GPIO fallback: {exc}"
        self.gpio = None
        self.pwms = {}
        print(f"[HW] {self.sim_gpio_reason}")

    # --- DS18B20 ---
    def read_temp_ds18b20(self, index: int) -> float:
        if self.sim or not self.ds_devices:
            base = 20.0 + self._sim_bias[min(index, len(self._sim_bias) - 1)]
            return base + random.uniform(-0.5, 0.5)
        if index >= len(self.ds_devices):
            index = len(self.ds_devices) - 1
        dev = self.ds_devices[index]
        try:
            with open(os.path.join(dev, "w1_slave"), "r") as f:
                lines = f.readlines()
            if len(lines) < 2 or "YES" not in lines[0]:
                raise RuntimeError("CRC inválido")
            temp_str = lines[1].split("t=")[-1].strip()
            return float(temp_str) / 1000.0
        except Exception as e:
            if not self._last_temp_error:
                print(f"[HW] Error leyendo {dev}: {e}. Usando 20°C de respaldo.")
                self._last_temp_error = True
            return 20.0
        finally:
            self._last_temp_error = False

    # --- Relés ---
    def setup_relay(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.setup(pin, self.gpio.OUT)
            self.gpio.output(pin, self.gpio.HIGH)
        except Exception as e:
            self._gpio_fallback(e)

    def relay_on(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.output(pin, self.gpio.LOW)
        except Exception as e:
            self._gpio_fallback(e)

    def relay_off(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.output(pin, self.gpio.HIGH)
        except Exception as e:
            self._gpio_fallback(e)

    # --- Stepper ---
    def setup_stepper(self, name: str, pul: int, direction: int, freq: float):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            GPIO = self.gpio
            GPIO.setup(direction, GPIO.OUT)
            GPIO.output(direction, GPIO.LOW)
            GPIO.setup(pul, GPIO.OUT)
            pwm = GPIO.PWM(pul, max(1, int(freq)))
            self.pwms[name] = {"pwm": pwm, "dir": direction, "pul": pul}
        except Exception as e:
            self._gpio_fallback(e)

    def start_stepper(self, name: str, freq: float):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        if name not in self.pwms:
            return
        try:
            pwm = self.pwms[name]["pwm"]
            pwm.ChangeFrequency(max(1, int(freq)))
            pwm.start(1)
        except Exception as e:
            self._gpio_fallback(e)

    def stop_stepper(self, name: str):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        if name not in self.pwms:
            return
        try:
            pwm = self.pwms[name]["pwm"]
            pwm.stop()
            self.gpio.output(self.pwms[name]["dir"], self.gpio.LOW)
        except Exception as e:
            self._gpio_fallback(e)

    def cleanup(self):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.cleanup()
        except Exception:
            pass


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

    def set_on(self, on: bool):
        self.set_color("#22c55e" if on else "#ef4444")


# ===== Calendario por FECHAS =====
DAYS_SHORT = ["L", "Ma", "Mi", "J", "V", "S", "D"]


class DateCalendarDialog(tk.Toplevel):
    def __init__(self, master, title_label, value_label, value_type=float, initial=None, import_callback=None):
        super().__init__(master)
        self.title(title_label)
        self.geometry("840x540")
        self.resizable(False, False)
        self.transient(master)
        self.grab_set()

        self.value_type = value_type
        self.data = {}
        self.import_callback = import_callback
        if isinstance(initial, dict):
            for k, v in initial.items():
                self.data[k] = [dict(ev) for ev in v]

        self.today = dt.date.today()
        self.selected_date = self.today
        self.view_year = self.today.year
        self.view_month = self.today.month

        container = ttk.Frame(self, padding=10)
        container.grid(row=0, column=0, sticky="nsew")
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)

        left = ttk.Frame(container)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        right = ttk.Frame(container)
        right.grid(row=0, column=1, sticky="nsew")

        container.columnconfigure(0, weight=0)
        container.columnconfigure(1, weight=1)
        container.rowconfigure(0, weight=1)

        nav = ttk.Frame(left)
        nav.grid(row=0, column=0, sticky="ew")
        ttk.Button(nav, text="◀", width=3, command=self.prev_month).grid(row=0, column=0, padx=2)
        self.lbl_month = ttk.Label(nav, text="", font=("Segoe UI", 12, "bold"))
        self.lbl_month.grid(row=0, column=1, padx=4)
        ttk.Button(nav, text="▶", width=3, command=self.next_month).grid(row=0, column=2, padx=2)
        nav.columnconfigure(1, weight=1)

        self.cal_grid = ttk.Frame(left)
        self.cal_grid.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        for c in range(7):
            self.cal_grid.columnconfigure(c, weight=1, uniform="days")
        for col, d in enumerate(DAYS_SHORT):
            ttk.Label(self.cal_grid, text=d, width=4, anchor="center").grid(
                row=0, column=col, padx=2, pady=2, sticky="nsew"
            )

        ttk.Label(right, text="Fecha seleccionada:", font=("Segoe UI", 10, "bold")).grid(row=0, column=0, sticky="w")
        self.lbl_sel = ttk.Label(right, text="")
        self.lbl_sel.grid(row=1, column=0, sticky="w", pady=(0, 6))

        self.listbox = tk.Listbox(right, height=16)
        self.listbox.grid(row=2, column=0, sticky="nsew")
        sb = ttk.Scrollbar(right, orient="vertical", command=self.listbox.yview)
        sb.grid(row=2, column=1, sticky="ns")
        self.listbox.config(yscrollcommand=sb.set)

        form = ttk.Frame(right)
        form.grid(row=3, column=0, sticky="ew", pady=8)
        ttk.Label(form, text="Hora (HH:MM):").grid(row=0, column=0, padx=4, pady=2, sticky="e")
        self.time_var = tk.StringVar(value="08:00")
        ttk.Entry(form, textvariable=self.time_var, width=8, justify="center").grid(row=0, column=1, padx=4, pady=2)

        ttk.Label(form, text=value_label).grid(row=1, column=0, padx=4, pady=2, sticky="e")
        self.val_var = tk.StringVar(value="20.0")
        ttk.Entry(form, textvariable=self.val_var, width=10, justify="center").grid(row=1, column=1, padx=4, pady=2)

        btns = ttk.Frame(right)
        btns.grid(row=4, column=0, sticky="ew", pady=(0, 4))
        ttk.Button(btns, text="Agregar", command=self.add_event).grid(row=0, column=0, padx=4)
        ttk.Button(btns, text="Editar", command=self.edit_event).grid(row=0, column=1, padx=4)
        ttk.Button(btns, text="Borrar", command=self.del_event).grid(row=0, column=2, padx=4)
        ttk.Button(btns, text="Borrar todo (día)", command=self.clear_day).grid(row=0, column=3, padx=4)
        if self.import_callback:
            ttk.Button(btns, text="Importar CSV/Excel", command=self.import_file).grid(
                row=1, column=0, columnspan=4, padx=4, pady=(6, 0)
            )

        right.rowconfigure(2, weight=1)

        sep = ttk.Separator(self, orient="horizontal")
        sep.grid(row=1, column=0, sticky="ew", padx=10, pady=(6, 0))
        footer = ttk.Frame(self, padding=(10, 6))
        footer.grid(row=2, column=0, sticky="e")
        ttk.Button(footer, text="Aceptar", command=self.accept).grid(row=0, column=0, padx=6)
        ttk.Button(footer, text="Cancelar", command=self.cancel).grid(row=0, column=1, padx=6)

        self.styles = {
            "normal_bg": self.cget("bg"),
            "today_bg": "#BEE3F8",
            "has_bg": "#C6F6D5",
            "other_bg": "#EDF2F7",
            "disabled_bg": "#E2E8F0",
        }

        self.day_buttons = []
        self.refresh_calendar()
        self.refresh_day_list()

    def month_title(self):
        return f"{MESES_ES[self.view_month]} {self.view_year}"

    def refresh_calendar(self):
        for child in list(self.cal_grid.grid_slaves()):
            info = child.grid_info()
            if int(info["row"]) > 0:
                child.destroy()

        self.lbl_month.config(text=self.month_title())
        self.day_buttons.clear()

        cal = pycal.Calendar(firstweekday=0)
        weeks = cal.monthdatescalendar(self.view_year, self.view_month)

        for r, week in enumerate(weeks, start=1):
            for c, d in enumerate(week):
                btn = tk.Button(
                    self.cal_grid,
                    text=str(d.day),
                    width=4,
                    relief="raised",
                    bd=1,
                    command=lambda dd=d: self.select_date(dd),
                )
                btn.grid(row=r, column=c, padx=2, pady=2, sticky="nsew")

                is_other_month = d.month != self.view_month
                is_past = d < self.today
                has_ev = ymd(d) in self.data and len(self.data[ymd(d)]) > 0
                is_today = d == self.today

                if is_past:
                    btn.config(
                        state="disabled",
                        bg=self.styles["disabled_bg"],
                        activebackground=self.styles["disabled_bg"],
                    )
                else:
                    bg = self.styles["other_bg"] if is_other_month else self.styles["normal_bg"]
                    if has_ev:
                        bg = self.styles["has_bg"]
                    if is_today:
                        bg = self.styles["today_bg"] if not has_ev else "#9AE6B4"
                    btn.config(bg=bg, activebackground=bg)

                if d == self.selected_date:
                    btn.config(relief="sunken")

                self.day_buttons.append((btn, d))

        self.lbl_sel.config(text=ymd(self.selected_date))

    def select_date(self, date_obj: dt.date):
        if date_obj < self.today:
            return
        self.selected_date = date_obj
        self.refresh_calendar()
        self.refresh_day_list()

    def prev_month(self):
        y, m = self.view_year, self.view_month
        if m == 1:
            y, m = y - 1, 12
        else:
            m -= 1
        self.view_year, self.view_month = y, m
        self.refresh_calendar()

    def next_month(self):
        y, m = self.view_year, self.view_month
        if m == 12:
            y, m = y + 1, 1
        else:
            m += 1
        self.view_year, self.view_month = y, m
        self.refresh_calendar()

    def refresh_day_list(self):
        self.listbox.delete(0, tk.END)
        flist = self.data.get(ymd(self.selected_date), [])
        for it in sorted(flist, key=lambda x: x["time"]):
            self.listbox.insert(tk.END, f"{it['time']}  •  {it['value']}")

    def _sel_index(self):
        sel = self.listbox.curselection()
        return sel[0] if sel else None

    def add_event(self):
        if self.selected_date < self.today:
            messagebox.showerror("Calendario", "No se pueden programar días anteriores al actual.")
            return
        t = self.time_var.get().strip()
        if not hhmm_ok(t):
            messagebox.showerror("Calendario", "Hora inválida (HH:MM).")
            return
        try:
            val = self.value_type(self.val_var.get().strip())
        except Exception:
            messagebox.showerror("Calendario", "Valor inválido.")
            return
        key = ymd(self.selected_date)
        self.data.setdefault(key, []).append({"time": t, "value": val})
        self.refresh_day_list()
        self.refresh_calendar()

    def edit_event(self):
        idx = self._sel_index()
        if idx is None:
            return
        key = ymd(self.selected_date)
        flist = sorted(self.data.get(key, []), key=lambda x: x["time"])
        if not flist:
            return
        t = self.time_var.get().strip()
        if not hhmm_ok(t):
            messagebox.showerror("Calendario", "Hora inválida (HH:MM).")
            return
        try:
            val = self.value_type(self.val_var.get().strip())
        except Exception:
            messagebox.showerror("Calendario", "Valor inválido.")
            return
        old = flist[idx]
        orig = self.data[key].index(old)
        self.data[key][orig] = {"time": t, "value": val}
        self.refresh_day_list()
        self.refresh_calendar()

    def del_event(self):
        idx = self._sel_index()
        if idx is None:
            return
        key = ymd(self.selected_date)
        flist = sorted(self.data.get(key, []), key=lambda x: x["time"])
        if not flist:
            return
        self.data[key].remove(flist[idx])
        if not self.data[key]:
            del self.data[key]
        self.refresh_day_list()
        self.refresh_calendar()

    def clear_day(self):
        key = ymd(self.selected_date)
        if key in self.data and self.data[key]:
            if messagebox.askyesno("Calendario", f"¿Borrar todos los eventos del {key}?"):
                del self.data[key]
                self.refresh_day_list()
                self.refresh_calendar()

    def import_file(self):
        if not self.import_callback:
            return
        data = self.import_callback()
        if data:
            self.data = data
            self.refresh_day_list()
            self.refresh_calendar()

    def accept(self):
        self.grab_release()
        self.destroy()

    def cancel(self):
        self.data = None
        self.grab_release()
        self.destroy()


# ===== Funciones calendario =====
def sp_from_date_calendar(events_dict: dict | None, t: dt.datetime, default=None):
    if not events_dict:
        return default
    key = ymd(t.date())
    flist = events_dict.get(key, [])
    if not flist:
        return default
    hhmm_now = t.strftime("%H:%M")
    todays = [e for e in flist if e.get("time") and e["time"] <= hhmm_now]
    if not todays:
        return default
    todays = sorted(todays, key=lambda e: e["time"])
    return todays[-1].get("value", default)


def nut_fire_for_minute(events_dict: dict | None, t: dt.datetime):
    if not events_dict:
        return []
    key = ymd(t.date())
    flist = events_dict.get(key, [])
    if not flist:
        return []
    hhmm_now = t.strftime("%H:%M")
    return [e.get("value") for e in flist if e.get("time") == hhmm_now]


def _events_from_rows(rows, value_type=float):
    events = {}
    for row in rows:
        date_raw = row.get("date") or row.get("fecha") or row.get("dia") or row.get("d")
        time_raw = row.get("time") or row.get("hora") or row.get("t")
        val_raw = row.get("value") or row.get("valor") or row.get("v")
        if not date_raw or not time_raw or val_raw is None:
            continue
        date_obj = _normalize_date(str(date_raw))
        if not date_obj:
            continue
        hhmm = str(time_raw).strip()
        if not hhmm_ok(hhmm):
            continue
        try:
            val = value_type(val_raw)
        except Exception:
            continue
        key = ymd(date_obj)
        events.setdefault(key, []).append({"time": hhmm, "value": val})
    return events


def _load_calendar_file(path: str, value_type=float):
    ext = os.path.splitext(path)[1].lower()
    if ext in {".csv", ".txt"}:
        with open(path, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))
        return _events_from_rows(rows, value_type=value_type)
    if ext in {".xlsx", ".xls"}:
        pd_spec = importlib_util.find_spec("pandas")
        if not pd_spec:
            raise RuntimeError("Necesitas instalar pandas para leer archivos de Excel (.xlsx/.xls)")
        import pandas as pd  # type: ignore

        df = pd.read_excel(path)
        rows = df.to_dict(orient="records")
        return _events_from_rows(rows, value_type=value_type)
    raise RuntimeError("Formato no soportado. Usa CSV o Excel.")


# ===== Fermentador (panel industrial) =====
class FermenterPanel(ctk.CTkFrame):
    def __init__(self, app, name, hw: Hardware, backup_path_getter):
        super().__init__(
            app,
            corner_radius=25,
            border_width=2,
            border_color="#111827",
            fg_color="#020617",
        )
        self.app = app
        self.name = name
        self.hw = hw
        self.get_backup_path = backup_path_getter

        if self.hw.sim:
            self.t = 21.5 + random.uniform(-0.3, 0.3)
            self._sim_ambient = 21.0 + random.uniform(-0.4, 0.4)
        else:
            self.t = self.hw.read_temp_ds18b20(index=int(self.name[1:]) - 1)
            self._sim_ambient = None
        self._last_update = now()
        self.t_str = tk.StringVar(value=f"{self.t:.1f}")
        self.sp = tk.DoubleVar(value=20.0)
        self.band = tk.DoubleVar(value=0.5)
        self.manual_mode = tk.BooleanVar(value=False)

        self.cold_in = False
        self.hot_in = False

        self.cal_sp = {}
        self.cal_nut = {}

        self.nut_running_until = None
        self._nut_led_on = False
        self._last_min = None
        self.freq_nut = tk.DoubleVar(value=8000.0)
        self.manual_nut_on = False

        self.csv_dir = tk.StringVar(value=os.path.abspath("./Proceso"))
        self.csv_name = tk.StringVar(value=f"{self.name}.csv")
        self._csv_running = False
        self._csv_paused = False
        self._csv_last_export_ok = False
        os.makedirs(self.csv_dir.get(), exist_ok=True)

        rel = RELAY_PINS[self.name]
        self.relay_cold = rel["cold"]
        self.relay_hot = rel["hot"]
        self.stepper_name = self.name
        step = STEPPER_PINS[self.name]
        if not hw.sim:
            hw.setup_relay(self.relay_cold)
            hw.setup_relay(self.relay_hot)
            hw.setup_stepper(self.stepper_name, step["pul"], step["dir"], 50)

        self._build_ui()

    # ---------------- UI ----------------
    def _build_ui(self):
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(99, weight=1)

        title = ctk.CTkLabel(
            self,
            text=f"Fermentador {self.name}",
            font=("Segoe UI", 20, "bold"),
        )
        title.grid(row=0, column=0, pady=(12, 8), sticky="w", padx=16)

        # Frame para T, SP y banda
        top = ctk.CTkFrame(self, fg_color="#020617")
        top.grid(row=1, column=0, sticky="ew", padx=16)
        top.grid_columnconfigure((0, 1, 2), weight=1, uniform="cols")

        # T
        ctk.CTkLabel(top, text="T (°C)", font=("Segoe UI", 13)).grid(row=0, column=0, pady=(0, 4))
        temp_box = ctk.CTkFrame(top, fg_color="#020617")
        temp_box.grid(row=1, column=0, pady=(0, 8))
        ctk.CTkLabel(
            temp_box,
            textvariable=self.t_str,
            font=("Segoe UI", 28, "bold"),
            text_color="#f97316",
        ).pack(padx=4, pady=4)

        # SP (con caja similar a T)
        ctk.CTkLabel(top, text="SP (°C)", font=("Segoe UI", 13)).grid(row=0, column=1, pady=(0, 4))
        sp_box = ctk.CTkFrame(top, fg_color="#020617")
        sp_box.grid(row=1, column=1, pady=(0, 8))
        ctk.CTkEntry(
            sp_box,
            textvariable=self.sp,
            width=80,
            justify="center",
            font=("Segoe UI", 18, "bold"),
        ).pack(padx=4, pady=4)

        # Banda (con caja similar a T)
        ctk.CTkLabel(top, text="Banda (°C)", font=("Segoe UI", 13)).grid(row=0, column=2, pady=(0, 4))
        band_box = ctk.CTkFrame(top, fg_color="#020617")
        band_box.grid(row=1, column=2, pady=(0, 8))
        ctk.CTkEntry(
            band_box,
            textvariable=self.band,
            width=80,
            justify="center",
            font=("Segoe UI", 18, "bold"),
        ).pack(padx=4, pady=4)

        # Modo manual
        ctk.CTkCheckBox(
            self,
            text="Modo manual (forzar)",
            variable=self.manual_mode,
            font=("Segoe UI", 13),
        ).grid(row=2, column=0, sticky="w", padx=20, pady=(4, 8))

        # LEDs Caliente / Fría
        hot_cold_frame = ctk.CTkFrame(self, fg_color="#020617")
        hot_cold_frame.grid(row=3, column=0, sticky="w", padx=20, pady=(0, 8))

        ctk.CTkLabel(hot_cold_frame, text="Caliente", font=("Segoe UI", 13)).grid(row=0, column=0, padx=(0, 4))
        self.led_hot_in = Led(hot_cold_frame)
        self.led_hot_in.widget().grid(row=0, column=1, padx=(0, 16))

        ctk.CTkLabel(hot_cold_frame, text="Fría", font=("Segoe UI", 13)).grid(row=0, column=2, padx=(0, 4))
        self.led_cold_in = Led(hot_cold_frame)
        self.led_cold_in.widget().grid(row=0, column=3)

        self._sync_leds()

        # Botones frío / caliente
        btn_row = ctk.CTkFrame(self, fg_color="#020617")
        btn_row.grid(row=4, column=0, sticky="ew", padx=16, pady=(4, 4))
        btn_row.grid_columnconfigure((0, 2), weight=1)

        ctk.CTkButton(
            btn_row,
            text="Forzar FRÍO",
            command=self.forzar_frio,
            fg_color="#0ea5e9",
            hover_color="#0284c7",
            corner_radius=20,
            height=34,
            width=160,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=0, column=0, padx=(0, 4), sticky="ew")

        ctk.CTkButton(
            btn_row,
            text="Cerrar TODO",
            command=self.cerrar_todo,
            fg_color="#4b5563",
            hover_color="#374151",
            corner_radius=20,
            height=34,
            width=140,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=0, column=1, padx=4, sticky="ew")

        ctk.CTkButton(
            btn_row,
            text="Forzar CALIENTE",
            command=self.forzar_caliente,
            fg_color="#f97316",
            hover_color="#ea580c",
            corner_radius=20,
            height=34,
            width=160,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=0, column=2, padx=(4, 0), sticky="ew")

        # Calendarios
        cal_row = ctk.CTkFrame(self, fg_color="#020617")
        cal_row.grid(row=5, column=0, sticky="ew", padx=16, pady=(4, 10))
        cal_row.grid_columnconfigure((0, 1), weight=1)

        ctk.CTkButton(
            cal_row,
            text="Calendario Setpoint",
            command=self.edit_cal_sp,
            fg_color="#6b7280",
            hover_color="#4b5563",
            corner_radius=20,
            height=32,
            width=170,
            font=("Segoe UI", 13, "bold"),
        ).grid(row=0, column=0, padx=(0, 4), sticky="ew")

        ctk.CTkButton(
            cal_row,
            text="Calendario Nutrición",
            command=self.edit_cal_nut,
            fg_color="#6b7280",
            hover_color="#4b5563",
            corner_radius=20,
            height=32,
            width=170,
            font=("Segoe UI", 13, "bold"),
        ).grid(row=0, column=1, padx=(4, 0), sticky="ew")

        # Nutrición + frecuencia
        nut_frame = ctk.CTkFrame(self, fg_color="#020617")
        nut_frame.grid(row=6, column=0, sticky="ew", padx=16, pady=(4, 4))
        nut_frame.grid_columnconfigure(1, weight=1)

        ctk.CTkLabel(nut_frame, text="Nutrición en curso:", font=("Segoe UI", 13)).grid(row=0, column=0, sticky="w")
        self.led_nut = Led(nut_frame)
        self.led_nut.widget().grid(row=0, column=1, sticky="w", padx=(4, 0))

        ctk.CTkLabel(nut_frame, text="Frecuencia bomba (Hz):", font=("Segoe UI", 13)).grid(
            row=1,
            column=0,
            sticky="w",
            pady=(6, 0),
        )
        ctk.CTkEntry(
            nut_frame,
            textvariable=self.freq_nut,
            width=90,
            justify="center",
            font=("Segoe UI", 13),
        ).grid(row=1, column=1, sticky="w", padx=(4, 0), pady=(6, 0))

        # Bomba manual
        self.btn_manual_nut = ctk.CTkButton(
            self,
            text="Bomba manual OFF",
            command=self.toggle_manual_nut,
            fg_color="#dc2626",
            hover_color="#b91c1c",
            corner_radius=20,
            height=36,
            font=("Segoe UI", 14, "bold"),
        )
        self.btn_manual_nut.grid(row=7, column=0, padx=16, pady=(8, 10), sticky="ew")
        self._update_manual_nut_button()

        # CSV frame
        csv_box = ctk.CTkFrame(self, fg_color="#020617", corner_radius=20, border_width=1, border_color="#1f2937")
        csv_box.grid(row=8, column=0, padx=16, pady=(4, 12), sticky="nsew")
        csv_box.grid_columnconfigure(1, weight=1)

        ctk.CTkLabel(csv_box, text="CSV", font=("Segoe UI", 16, "bold")).grid(
            row=0,
            column=0,
            columnspan=3,
            sticky="w",
            padx=12,
            pady=(8, 4),
        )

        ctk.CTkLabel(csv_box, text="Carpeta:", font=("Segoe UI", 13)).grid(
            row=1,
            column=0,
            sticky="e",
            padx=(12, 4),
            pady=2,
        )
        ctk.CTkEntry(csv_box, textvariable=self.csv_dir, font=("Segoe UI", 12)).grid(
            row=1,
            column=1,
            sticky="ew",
            pady=2,
        )
        ctk.CTkButton(
            csv_box,
            text="...",
            width=40,
            command=self.pick_dir,
            corner_radius=12,
        ).grid(row=1, column=2, sticky="w", padx=(4, 12), pady=2)

        ctk.CTkLabel(csv_box, text="Archivo:", font=("Segoe UI", 13)).grid(
            row=2,
            column=0,
            sticky="e",
            padx=(12, 4),
            pady=2,
        )
        ctk.CTkEntry(csv_box, textvariable=self.csv_name, font=("Segoe UI", 12)).grid(
            row=2,
            column=1,
            sticky="ew",
            pady=2,
        )

        # Botones CSV
        btn_csv_row = ctk.CTkFrame(csv_box, fg_color="#020617")
        btn_csv_row.grid(row=3, column=0, columnspan=3, pady=(6, 4), padx=12, sticky="ew")
        btn_csv_row.grid_columnconfigure((0, 1, 2, 3), weight=1, uniform="csv")

        def _mk_csv_btn(text, cmd):
            return ctk.CTkButton(
                btn_csv_row,
                text=text,
                command=cmd,
                height=30,
                width=120,
                corner_radius=18,
                font=("Segoe UI", 12, "bold"),
            )

        _mk_csv_btn("Inicio/Reanudar", self.csv_start).grid(row=0, column=0, padx=2, sticky="ew")
        _mk_csv_btn("Pausar/Detener", self.csv_pause).grid(row=0, column=1, padx=2, sticky="ew")
        _mk_csv_btn("Exportar CSV", self.csv_export).grid(row=0, column=2, padx=2, sticky="ew")
        _mk_csv_btn("Borrar/Reiniciar", self.csv_restart).grid(row=0, column=3, padx=2, sticky="ew")

        # Estado CSV + gráfico
        state_row = ctk.CTkFrame(csv_box, fg_color="#020617")
        state_row.grid(row=4, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 10))
        state_row.grid_columnconfigure(1, weight=1)

        ctk.CTkLabel(state_row, text="Estado:", font=("Segoe UI", 13)).grid(row=0, column=0, sticky="w")
        self.led_csv = Led(state_row)
        self.led_csv.widget().grid(row=0, column=1, sticky="w", padx=(4, 12))
        self._csv_state_led("red")

        ctk.CTkButton(
            state_row,
            text="Gráfico tiempo real",
            command=lambda: self.app.open_realtime_plot(self.name),
            fg_color="#22c55e",
            hover_color="#16a34a",
            corner_radius=22,
            height=34,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=1, column=0, columnspan=3, pady=(8, 2), sticky="ew")

        ctk.CTkButton(
            state_row,
            text="Gráfico caudal CO2",
            command=lambda: self.app.open_flow_plot(self.name),
            fg_color="#3b82f6",
            hover_color="#2563eb",
            corner_radius=22,
            height=32,
            font=("Segoe UI", 13, "bold"),
        ).grid(row=2, column=0, columnspan=3, pady=(6, 2), sticky="ew")

    # --------- Forzados y LEDs ----------
    def _sync_leds(self):
        self.led_cold_in.set_on(self.cold_in)
        self.led_hot_in.set_on(self.hot_in)

    def _update_manual_nut_button(self):
        if self.manual_nut_on:
            self.btn_manual_nut.configure(
                text="Bomba manual ON",
                fg_color="#16a34a",
                hover_color="#15803d",
            )
        else:
            self.btn_manual_nut.configure(
                text="Bomba manual OFF",
                fg_color="#dc2626",
                hover_color="#b91c1c",
            )

    def _can_force(self):
        return self.manual_mode.get()

    def forzar_frio(self):
        if not self._can_force():
            return
        self.cold_in = True
        self.hot_in = False
        self._apply_relays()
        self._sync_leds()

    def forzar_caliente(self):
        if not self._can_force():
            return
        self.hot_in = True
        self.cold_in = False
        self._apply_relays()
        self._sync_leds()

    def cerrar_todo(self):
        self.cold_in = False
        self.hot_in = False
        self._apply_relays()
        self._sync_leds()

    def stop_all(self):
        self.manual_mode.set(True)
        self.cold_in = False
        self.hot_in = False
        self.nut_running_until = None
        self.manual_nut_on = False
        self._apply_nutricion_state(False)
        self._apply_relays()
        self._sync_leds()
        self._update_manual_nut_button()

    def _apply_relays(self):
        if self.cold_in:
            self.hw.relay_on(self.relay_cold)
        else:
            self.hw.relay_off(self.relay_cold)
        if self.hot_in:
            self.hw.relay_on(self.relay_hot)
        else:
            self.hw.relay_off(self.relay_hot)

    def toggle_manual_nut(self):
        self.manual_nut_on = not self.manual_nut_on
        self._update_manual_nut_button()
        tnow = now()
        schedule_active = bool(self.nut_running_until and tnow < self.nut_running_until)
        self._apply_nutricion_state(schedule_active or self.manual_nut_on)

    # -------------- Calendarios --------------
    def edit_cal_sp(self):
        dlg = DateCalendarDialog(
            self.app,
            title_label=f"Calendario de Setpoint – {self.name}",
            value_label="Setpoint (°C):",
            value_type=float,
            initial=self.cal_sp,
            import_callback=lambda: self._import_calendar(value_type=float),
        )
        self.app.wait_window(dlg)
        if dlg.data is not None:
            self.cal_sp = dlg.data

    def edit_cal_nut(self):
        dlg = DateCalendarDialog(
            self.app,
            title_label=f"Calendario de Nutrición – {self.name}",
            value_label="Duración (seg):",
            value_type=float,
            initial=self.cal_nut,
            import_callback=lambda: self._import_calendar(value_type=float),
        )
        self.app.wait_window(dlg)
        if dlg.data is not None:
            self.cal_nut = dlg.data

    def _import_calendar(self, value_type=float):
        path = filedialog.askopenfilename(
            title="Importar calendario (CSV/Excel)",
            filetypes=[
                ("CSV", "*.csv"),
                ("Excel", "*.xlsx *.xls"),
                ("Todos", "*.*"),
            ],
        )
        _restore_focus(self)
        if not path:
            return None
        try:
            data = _load_calendar_file(path, value_type=value_type)
            if not data:
                messagebox.showwarning("Importar calendario", "El archivo no tiene filas válidas (fecha, hora, valor).")
                return None
            return data
        except Exception as e:
            messagebox.showerror("Importar calendario", f"No se pudo importar el archivo.\n{e}")
            return None

    def _apply_nutricion_state(self, should_run: bool):
        if should_run and not self._nut_led_on:
            self.hw.start_stepper(self.stepper_name, self.freq_nut.get())
        elif not should_run and self._nut_led_on:
            self.hw.stop_stepper(self.stepper_name)
        self._nut_led_on = should_run
        self.led_nut.set_on(self._nut_led_on)

    # ---------------- CSV --------------------
    def pick_dir(self):
        d = filedialog.askdirectory(title="Elegir carpeta de trabajo CSV")
        _restore_focus(self)
        if d:
            self.csv_dir.set(d)
            os.makedirs(d, exist_ok=True)

    def _csv_path(self):
        name = self.csv_name.get().strip() or f"{self.name}.csv"
        if not name.lower().endswith(".csv"):
            name += ".csv"
        return os.path.join(self.csv_dir.get(), name)

    def _csv_state_led(self, color):
        self.led_csv.set_color(color)

    def csv_start(self):
        self._csv_running = True
        self._csv_paused = False
        self._csv_last_export_ok = False
        self._csv_state_led("#22c55e")

    def csv_pause(self):
        self._csv_running = False
        self._csv_paused = True
        self._csv_state_led("#eab308")

    def csv_export(self):
        if self._csv_running:
            messagebox.showerror("Exportar", "Detén o pausa el CSV antes de exportar.")
            return
        src = self._csv_path()
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
            self._csv_last_export_ok = True
            self._csv_state_led("#3b82f6")
            messagebox.showinfo("Exportar", f"Archivo exportado a:\n{dst}")
        except Exception as e:
            messagebox.showerror("Exportar", f"No se pudo exportar.\n{e}")

    def csv_restart(self):
        self._csv_running = False
        self._csv_paused = False
        path = self._csv_path()
        try:
            if os.path.exists(path):
                os.remove(path)
            self._csv_state_led("#ef4444")
            messagebox.showinfo("CSV", f"Archivo reiniciado:\n{path}")
        except Exception as e:
            messagebox.showerror("CSV", f"No se pudo reiniciar.\n{e}")

    def _csv_write_row(self):
        row = {
            "timestamp": now_str(),
            "fermentador": self.name,
            "T": f"{self.t:.1f}",
            "SP": f"{float(self.sp.get()):.2f}",
            "banda": f"{float(self.band.get()):.2f}",
            "cold": int(self.cold_in),
            "hot": int(self.hot_in),
            "nutricion_activa": int(self._nut_led_on),
            "freq_nut": f"{float(self.freq_nut.get()):.1f}",
        }

        if self._csv_running:
            ipath = self._csv_path()
            cabe = not os.path.exists(ipath)
            try:
                os.makedirs(os.path.dirname(ipath), exist_ok=True)
                with open(ipath, "a", newline="", encoding="utf-8") as f:
                    w = csv.DictWriter(f, fieldnames=list(row.keys()))
                    if cabe:
                        w.writeheader()
                    w.writerow(row)
            except Exception as e:
                messagebox.showerror("CSV", f"No se pudo escribir en {ipath}\n{e}")

        bpath = self.get_backup_path()
        bdir = os.path.dirname(bpath) or "."
        os.makedirs(bdir, exist_ok=True)

        backup_fields = [
            "timestamp",
            "fermentador",
            "T",
            "SP",
            "banda",
            "cold",
            "hot",
            "nutricion_activa",
            "freq_nut",
        ]
        write_header = not os.path.exists(bpath) or os.path.getsize(bpath) == 0

        try:
            with open(bpath, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=backup_fields, extrasaction="ignore")
                if write_header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("Backup global", f"No se pudo escribir en {bpath}\n{e}")

    # ----------------- Simulación de temperatura -----------------
    def _simulate_temp(self, dt_seconds: float):
        if dt_seconds <= 0:
            return

        sp_obj = float(self.sp.get())

        ambient_pull = (self._sim_ambient - self.t) * 0.0008
        ferment_target = max(sp_obj, self._sim_ambient + 4.0)
        ferment_heat = (ferment_target - self.t) * 0.018

        heating = 0.22 if self.hot_in else 0.0
        cooling = -0.28 if self.cold_in else 0.0

        ruido = random.uniform(-0.008, 0.008)
        delta = (ambient_pull + ferment_heat + heating + cooling + ruido) * dt_seconds
        self.t = max(-5.0, min(40.0, self.t + delta))

    # ----------------- Loop del proceso -----------------
    def update_process(self):
        tnow = now()
        dt_seconds = max(0.001, (tnow - self._last_update).total_seconds())
        self._last_update = tnow

        sp_cal = None
        if not self.manual_mode.get():
            sp_cal = sp_from_date_calendar(self.cal_sp, tnow, default=None)
            if sp_cal is not None:
                try:
                    self.sp.set(float(sp_cal))
                except Exception:
                    pass

        current_min = tnow.strftime("%Y-%m-%d %H:%M")
        if self._last_min != current_min:
            doses = nut_fire_for_minute(self.cal_nut, tnow)
            if doses:
                dur_total = sum(float(d) for d in doses if float(d) > 0)
                if dur_total > 0:
                    self.nut_running_until = tnow + dt.timedelta(seconds=dur_total)
                    self.hw.start_stepper(self.stepper_name, self.freq_nut.get())
            self._last_min = current_min

        schedule_active = False
        if self.nut_running_until and tnow < self.nut_running_until:
            schedule_active = True
        else:
            self.nut_running_until = None
        self._apply_nutricion_state(schedule_active or self.manual_nut_on)

        if self.hw.sim:
            self._simulate_temp(dt_seconds)
        else:
            self.t = self.hw.read_temp_ds18b20(index=int(self.name[1:]) - 1)
        self.t_str.set(f"{self.t:.1f}")

        if not self.manual_mode.get():
            sp = float(self.sp.get())
            band = max(0.05, float(self.band.get()))
            # control frío
            if self.cold_in:
                if self.t <= sp - band:
                    self.cold_in = False
            else:
                if self.t >= sp + band:
                    self.cold_in = True
            # control caliente
            if self.hot_in:
                if self.t >= sp + band:
                    self.hot_in = False
            else:
                if self.t <= sp - band:
                    self.hot_in = True
            if not self.cold_in and not self.hot_in:
                self.cerrar_todo()
            self._apply_relays()
            self._sync_leds()

        self._csv_write_row()


# ===== App principal =====
class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("dark-blue")

        self.title("Panel de control – 3 Fermentadores")
        self.geometry("1500x780")
        self.minsize(1400, 850)

        self.grid_columnconfigure((0, 1, 2), weight=1, uniform="col")
        self.grid_rowconfigure(2, weight=1)

        self.hw = Hardware()
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
        default_channels = {"F1": 1, "F2": 2, "F3": 3}
        for name in ("F1", "F2", "F3"):
            addr_env = os.environ.get(f"ADS1115_ADDR_{name}", "").strip()
            ch_env = os.environ.get(f"ADS1115_CH_{name}", "").strip()
            gain_env = os.environ.get(f"ADS1115_GAIN_{name}", "").strip()
            addr = parse_int(addr_env, ADS1115_ADDR) if addr_env else ADS1115_ADDR
            default_ch = default_channels.get(name, ADS1115_CH)
            ch = parse_int(ch_env, default_ch) if ch_env else default_ch
            gain = parse_int(gain_env, ADS1115_GAIN) if gain_env else ADS1115_GAIN
            reader = ADS1115Reader(addr, ch, gain)
            self.flow_readers[name] = reader
            self.flow_samples[name] = []
            self.flow_next_sample[name] = None
            if SAMPLE_PERIOD_SEC is None:
                period = 1 if reader.sim else 10
            else:
                period = SAMPLE_PERIOD_SEC
            self.flow_sample_period[name] = period
            self.co2_csv_dir[name] = tk.StringVar(value=os.path.abspath("./Proceso"))
            self.co2_csv_name[name] = tk.StringVar(value=f"{name}_co2.csv")
            self.co2_csv_running[name] = False
            self.co2_csv_paused[name] = False
            self.co2_csv_last_export_ok[name] = False
            os.makedirs(self.co2_csv_dir[name].get(), exist_ok=True)
        self._flow_plot_windows = {}

        # ---------- LOGO CII ----------
        self.logo_ctk = None
        logo_path = os.path.join(ASSETS_DIR, "logo_cii.png")
        if os.path.exists(logo_path):
            try:
                pil_img = Image.open(logo_path)
                # tamaño objetivo (ajusta si quieres):
                self.logo_ctk = ctk.CTkImage(dark_image=pil_img, size=(160, 80))
            except Exception as e:
                print(f"[UI] No se pudo cargar el logo {logo_path}: {e}")
        else:
            print(f"[UI] Logo no encontrado en: {logo_path}")

        # TOP BAR
        top_bar = ctk.CTkFrame(self, fg_color="transparent")
        top_bar.grid(row=0, column=0, columnspan=3, sticky="ew", padx=12, pady=(10, 0))
        top_bar.grid_columnconfigure(0, weight=1)

        title_row = ctk.CTkFrame(top_bar, fg_color="transparent")
        title_row.grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(
            title_row,
            text="Panel 3 Fermentadores",
            font=("Segoe UI", 28, "bold"),
        ).pack(side="left")
        ctk.CTkLabel(
            title_row,
            text="  by Francisco Rojas",
            font=("Segoe UI", 18, "italic"),
        ).pack(side="left")

        mode_text = f"Modo: {'SIMULADOR' if self.hw.sim else 'HARDWARE'}"
        ctk.CTkLabel(
            top_bar,
            text=mode_text,
            font=("Segoe UI", 13, "italic"),
        ).grid(row=1, column=0, sticky="w", pady=(4, 0))

        if self.logo_ctk is not None:
            logo_label = ctk.CTkLabel(top_bar, image=self.logo_ctk, text="")
            logo_label.grid(row=0, column=1, rowspan=2, sticky="e", padx=(0, 10))

        # Backup global
        backup_frame = ctk.CTkFrame(self, fg_color="transparent")
        backup_frame.grid(row=1, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 8))
        backup_frame.grid_columnconfigure(1, weight=1)

        self.backup_path = tk.StringVar(value=os.path.abspath("./Backup/backup_global.csv"))
        ctk.CTkLabel(backup_frame, text="Backup global:", font=("Segoe UI", 13)).grid(row=0, column=0, sticky="w")
        ctk.CTkEntry(backup_frame, textvariable=self.backup_path, font=("Segoe UI", 12)).grid(
            row=0,
            column=1,
            sticky="ew",
            padx=(4, 4),
        )
        ctk.CTkButton(
            backup_frame,
            text="Destino…",
            command=self.pick_backup,
            height=30,
            corner_radius=16,
        ).grid(row=0, column=2, padx=(4, 0))

        # Fermentadores (menos espacio lateral)
        self.ferms = []
        for i in range(3):
            panel = FermenterPanel(self, f"F{i+1}", self.hw, backup_path_getter=self.get_backup_path)
            panel.grid(row=2, column=i, padx=8, pady=(4, 10), sticky="nsew")
            self.ferms.append(panel)

        # Footer
        footer = ctk.CTkFrame(self, fg_color="transparent")
        footer.grid(row=3, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 10))
        footer.grid_columnconfigure(0, weight=1)
        footer.grid_columnconfigure(1, weight=1)
        footer.grid_columnconfigure(2, weight=1)

        ctk.CTkButton(
            footer,
            text="DETENER TODO",
            command=self.cerrar_todo_global,
            fg_color="#ef4444",
            hover_color="#b91c1c",
            height=36,
            corner_radius=22,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=0, column=0, sticky="w")

        ctk.CTkButton(
            footer,
            text="Exportar CSV de todos",
            command=self.export_all,
            fg_color="#3b82f6",
            hover_color="#2563eb",
            height=36,
            corner_radius=22,
            font=("Segoe UI", 14, "bold"),
        ).grid(row=0, column=1, sticky="w", padx=(10, 0))

        self.clock_var = tk.StringVar(value=now_str())
        ctk.CTkLabel(footer, textvariable=self.clock_var, font=("Segoe UI", 14)).grid(
            row=0,
            column=2,
            sticky="e",
        )

        self._tick_job = None        
        self._plot_windows = []
        self._closing = False
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self._tick()

    # ===== util backup =====
    def get_backup_path(self):
        path = self.backup_path.get().strip()
        if not path:
            path = os.path.abspath("./Backup/backup_global.csv")
            self.backup_path.set(path)
        if not path.lower().endswith(".csv"):
            path += ".csv"
        d = os.path.dirname(path) or "."
        os.makedirs(d, exist_ok=True)
        return path

    def pick_backup(self):
        fn = filedialog.asksaveasfilename(
            title="Elegir archivo de BACKUP global",
            initialfile=os.path.basename(self.backup_path.get()),
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("Todos", "*.*")],
        )
        _restore_focus(self)
        if fn:
            self.backup_path.set(fn)
            os.makedirs(os.path.dirname(fn), exist_ok=True)

    def _read_recent_backup(self, days=10, fermenter=None):
        path = self.get_backup_path()
        if not os.path.exists(path):
            return {}
        cutoff = now() - dt.timedelta(days=days)
        data = {}
        with open(path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                ts_raw = (row.get("timestamp") or "").strip()
                ts = None
                for fmt in ("%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
                    try:
                        ts = dt.datetime.strptime(ts_raw, fmt)
                        break
                    except Exception:
                        continue
                if not ts or ts < cutoff:
                    continue
                ferm = row.get("fermentador", "?").strip() or "?"
                if fermenter and ferm != fermenter:
                    continue
                try:
                    temp = float(row.get("T", "nan"))
                    sp = float(row.get("SP", "nan"))
                    nut = int(row.get("nutricion_activa", "0") or 0)
                except Exception:
                    continue
                data.setdefault(ferm, {"ts": [], "t": [], "sp": [], "nut": []})
                data[ferm]["ts"].append(ts)
                data[ferm]["t"].append(temp)
                data[ferm]["sp"].append(sp)
                data[ferm]["nut"].append(nut)
        return data

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

    # ===== gráfico tiempo real CO2 =====
    def open_flow_plot(self, fermenter):
        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            return
        reader = self.flow_readers.get(fermenter)
        if reader is None:
            messagebox.showerror("Gráfico", f"No hay configuración de caudal para {fermenter}.")
            return
        existing = self._flow_plot_windows.get(fermenter)
        if existing is not None and existing.winfo_exists():
            try:
                existing.lift()
                existing.focus_force()
            except Exception:
                pass
            return

        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore

        top = tk.Toplevel(self)
        self._flow_plot_windows[fermenter] = top
        top.title(f"Caudal CO2 en tiempo real – {fermenter}")

        header = ttk.Frame(top)
        header.pack(fill="x", padx=8, pady=(8, 4))
        ttk.Label(header, text="Caudalímetro CO2 (4-20 mA)", font=("Segoe UI", 14, "bold")).pack(side="left")
        mode_text = "SIMULADOR" if reader.sim else "HARDWARE"
        mode_color = "#dc2626" if reader.sim else "#16a34a"
        ttk.Label(header, text=mode_text, foreground=mode_color).pack(side="right")

        stats = ttk.Frame(top)
        stats.pack(fill="x", padx=8, pady=(0, 6))
        stats.grid_columnconfigure(1, weight=1)

        flow_var = tk.StringVar(value="0.00 SCCM")
        current_var = tk.StringVar(value="0.00 mA")
        voltage_var = tk.StringVar(value="0.000 V")
        status_var = tk.StringVar(value="Esperando...")
        next_var = tk.StringVar(value="--:--:--")

        ttk.Label(stats, text="Caudal:", font=("Segoe UI", 12, "bold")).grid(row=0, column=0, sticky="w")
        ttk.Label(stats, textvariable=flow_var, font=("Segoe UI", 12)).grid(row=0, column=1, sticky="w")
        ttk.Label(stats, text="Corriente:", font=("Segoe UI", 12, "bold")).grid(row=2, column=0, sticky="w")
        ttk.Label(stats, textvariable=current_var, font=("Segoe UI", 12)).grid(row=2, column=1, sticky="w")
        ttk.Label(stats, text="Voltaje:", font=("Segoe UI", 12, "bold")).grid(row=3, column=0, sticky="w")
        ttk.Label(stats, textvariable=voltage_var, font=("Segoe UI", 12)).grid(row=3, column=1, sticky="w")
        ttk.Label(stats, text="Estado:", font=("Segoe UI", 12, "bold")).grid(row=4, column=0, sticky="w")
        ttk.Label(stats, textvariable=status_var, font=("Segoe UI", 12)).grid(row=4, column=1, sticky="w")
        ttk.Label(stats, text="Siguiente muestra:", font=("Segoe UI", 12, "bold")).grid(row=5, column=0, sticky="w")
        ttk.Label(stats, textvariable=next_var, font=("Segoe UI", 12)).grid(row=5, column=1, sticky="w")
        ttk.Label(stats, text="SCCM = cm3/min", font=("Segoe UI", 10, "italic")).grid(
            row=6, column=0, columnspan=2, sticky="w", pady=(4, 0)
        )

        control = ttk.Frame(top)
        control.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(control, text="Escala:").pack(side="left")

        current_window_hours = PLOT_WINDOW_HOURS if PLOT_WINDOW_HOURS > 0 else None

        def set_window(h):
            nonlocal current_window_hours
            current_window_hours = h
            refresh()

        for label, hours in [
            ("Tiempo real", None),
            ("1 h", 1),
            ("12 h", 12),
            ("24 h", 24),
            ("48 h", 48),
            ("72 h", 72),
            ("1 semana", 24 * 7),
            ("2 semanas", 24 * 14),
        ]:
            ttk.Button(control, text=label, command=lambda h=hours: set_window(h)).pack(side="left", padx=2)

        csv_box = ttk.Frame(top)
        csv_box.pack(fill="x", padx=8, pady=(0, 6))
        csv_box.grid_columnconfigure(1, weight=1)

        ttk.Label(csv_box, text="CSV CO2", font=("Segoe UI", 12, "bold")).grid(
            row=0, column=0, columnspan=3, sticky="w"
        )

        ttk.Label(csv_box, text="Carpeta:").grid(row=1, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(csv_box, textvariable=self.co2_csv_dir[fermenter]).grid(
            row=1, column=1, sticky="ew", pady=2
        )
        ttk.Button(csv_box, text="...", width=4, command=lambda: self.co2_pick_dir(fermenter)).grid(
            row=1, column=2, sticky="w", pady=2
        )

        ttk.Label(csv_box, text="Archivo:").grid(row=2, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(csv_box, textvariable=self.co2_csv_name[fermenter]).grid(
            row=2, column=1, sticky="ew", pady=2
        )

        btn_row = ttk.Frame(csv_box)
        btn_row.grid(row=3, column=0, columnspan=3, sticky="ew", pady=(6, 4))
        for i in range(4):
            btn_row.grid_columnconfigure(i, weight=1)

        ttk.Button(btn_row, text="Inicio/Reanudar", command=lambda: self.co2_csv_start(fermenter)).grid(
            row=0, column=0, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Pausar/Detener", command=lambda: self.co2_csv_pause(fermenter)).grid(
            row=0, column=1, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Exportar CSV", command=lambda: self.co2_csv_export(fermenter)).grid(
            row=0, column=2, padx=2, sticky="ew"
        )
        ttk.Button(btn_row, text="Borrar/Reiniciar", command=lambda: self.co2_csv_restart(fermenter)).grid(
            row=0, column=3, padx=2, sticky="ew"
        )

        state_row = ttk.Frame(csv_box)
        state_row.grid(row=4, column=0, columnspan=3, sticky="ew", pady=(2, 0))
        ttk.Label(state_row, text="Estado:").pack(side="left")
        led = Led(state_row)
        led.widget().pack(side="left", padx=6)
        self._co2_csv_leds[fermenter] = led
        if self.co2_csv_running.get(fermenter):
            led.set_color("#22c55e")
        elif self.co2_csv_paused.get(fermenter):
            led.set_color("#eab308")
        elif self.co2_csv_last_export_ok.get(fermenter):
            led.set_color("#3b82f6")
        else:
            led.set_color("#ef4444")

        fig, ax_flow = plt.subplots(
            1,
            1,
            figsize=(9, 6),
        )
        line_flow, = ax_flow.plot([], [], color="#2563eb", linewidth=2, label="Caudal")
        ax_flow.set_title("Caudal CO2 (SCCM)")
        ax_flow.set_ylabel("SCCM")
        ax_flow.grid(True, alpha=0.2)
        ax_flow.set_xlabel("Hora")
        ax_flow.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M"))

        canvas = FigureCanvasTkAgg(fig, master=top)
        canvas.get_tk_widget().pack(fill="both", expand=True)

        def windowed_samples(samples):
            if not samples:
                return []
            if current_window_hours is None:
                return samples
            right = samples[-1][0]
            left = right - dt.timedelta(hours=current_window_hours)
            return [row for row in samples if row[0] >= left]

        def update_plot():
            samples = self.flow_samples.get(fermenter, [])
            windowed = windowed_samples(samples)
            if not windowed:
                return
            times = [ts for ts, _, _, _, _ in windowed]
            values = [flow for _, flow, _, _, _ in windowed]
            line_flow.set_data(times, values)

            right = times[-1]
            if current_window_hours is None:
                left = times[0]
                if left == right:
                    left = right - dt.timedelta(seconds=max(1, self.flow_sample_period[fermenter]))
            else:
                left = right - dt.timedelta(hours=current_window_hours)
            ax_flow.set_xlim(left, right)

            vmin = min(values)
            vmax = max(values)
            pad = (vmax - vmin) * 0.1 if vmax != vmin else 1.0
            ax_flow.set_ylim(vmin - pad, vmax + pad)
            fig.autofmt_xdate()
            canvas.draw_idle()

        def update_stats():
            samples = self.flow_samples.get(fermenter, [])
            if not samples:
                flow_var.set("0.00 SCCM")
                current_var.set("0.00 mA")
                voltage_var.set("0.000 V")
                status_var.set("Esperando...")
                return
            _, flow, current_ma, voltage, status = samples[-1]
            flow_var.set(f"{flow:0.2f} SCCM")
            current_var.set(f"{current_ma:0.2f} mA")
            voltage_var.set(f"{voltage:0.3f} V")
            status_var.set(status)

        def update_countdown():
            next_sample = self.flow_next_sample.get(fermenter)
            if next_sample is None:
                next_var.set("--:--:--")
                return
            delta = next_sample - now()
            if delta.total_seconds() < 0:
                next_var.set("00:00:00")
            else:
                total = int(delta.total_seconds())
                hh = total // 3600
                mm = (total % 3600) // 60
                ss = total % 60
                next_var.set(f"{hh:02d}:{mm:02d}:{ss:02d}")

        def refresh():
            if not top.winfo_exists():
                return
            update_stats()
            update_plot()
            update_countdown()
            top._refresh_job = top.after(1000, refresh)

        def on_close_plot():
            if getattr(top, "_refresh_job", None) is not None:
                try:
                    top.after_cancel(top._refresh_job)
                except Exception:
                    pass
                top._refresh_job = None
            if top in self._plot_windows:
                self._plot_windows.remove(top)
            if self._flow_plot_windows.get(fermenter) is top:
                self._flow_plot_windows.pop(fermenter, None)
            self._co2_csv_leds.pop(fermenter, None)
            top.destroy()

        top.protocol("WM_DELETE_WINDOW", on_close_plot)
        self._plot_windows.append(top)
        refresh()

    # ===== gráfico tiempo real =====
    def open_realtime_plot(self, fermenter=None):
        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            return
        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore

        top = tk.Toplevel(self)
        title_suffix = f" – {fermenter}" if fermenter else " (todos)"
        top.title(f"Gráfico en tiempo real{title_suffix}")

        fig, (ax_temp, ax_nut) = plt.subplots(
            2,
            1,
            sharex=True,
            figsize=(9, 5),
            gridspec_kw={"height_ratios": [3, 1], "hspace": 0.1},
        )
        canvas = FigureCanvasTkAgg(fig, master=top)
        canvas.get_tk_widget().pack(fill="both", expand=True)

        control = ttk.Frame(top)
        control.pack(side="top", fill="x", padx=8, pady=4)
        ttk.Label(control, text="Rango eje X:").pack(side="left")

        current_window_hours = 10 * 24

        def set_window(h):
            nonlocal current_window_hours
            current_window_hours = h
            refresh()

        for label, hours in [
            ("10 días", 10 * 24),
            ("7 días", 7 * 24),
            ("2 días", 2 * 24),
            ("1 día", 24),
            ("12 h", 12),
            ("1 h", 1),
        ]:
            ttk.Button(control, text=label, command=lambda h=hours: set_window(h)).pack(side="left", padx=2)

        status = ttk.Label(top, text="Cargando datos…")
        status.pack(anchor="w", padx=8, pady=4)

        top._refresh_job = None
        self._plot_windows.append(top)

        def refresh():
            if not top.winfo_exists():
                return
            nonlocal current_window_hours
            days_window = current_window_hours / 24.0
            data = self._read_recent_backup(days=days_window, fermenter=fermenter)
            ax_temp.clear()
            ax_nut.clear()

            if not data:
                status.config(text="Sin datos recientes en el backup.")
            else:
                temps_all = []
                for ferm, series in sorted(data.items()):
                    if not series["ts"]:
                        continue
                    ax_temp.plot(series["ts"], series["t"], label=f"{ferm} T")
                    ax_temp.plot(series["ts"], series["sp"], linestyle="--", label=f"{ferm} SP")
                    temps_all.extend(series["t"])
                    nut = series.get("nut", [])
                    if nut and any(nut):
                        ax_nut.step(series["ts"], nut, where="post", color="red", alpha=0.8, label=f"{ferm} Nutrición")

                ax_temp.set_title("Temperatura vs. tiempo")
                ax_temp.set_ylabel("°C")

                if temps_all:
                    tmin = min(temps_all)
                    tmax = max(temps_all)
                    pad = (tmax - tmin) * 0.1 if tmax != tmin else 1.0
                    ax_temp.set_ylim(tmin - pad, tmax + pad)

                ax_nut.set_ylabel("Nutrición ON=1")
                ax_nut.set_ylim(-0.1, 1.1)
                ax_nut.set_yticks([0, 1])
                ax_nut.set_xlabel("Fecha y hora")

                ax_nut.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))
                fig.autofmt_xdate()

                lines1, labels1 = ax_temp.get_legend_handles_labels()
                lines2, labels2 = ax_nut.get_legend_handles_labels()
                if lines1 or lines2:
                    ax_temp.legend(lines1 + lines2, labels1 + labels2, loc="upper left")

                right = now()
                left = right - dt.timedelta(hours=current_window_hours)
                ax_temp.set_xlim(left, right)

                if current_window_hours >= 24:
                    rango = f"últimos {int(current_window_hours // 24)} días"
                else:
                    rango = f"últimas {current_window_hours} horas"
                status.config(text=f"Fuente: backup global ({rango})")

            canvas.draw()
            top._refresh_job = top.after(5000, refresh)

        def on_close_plot():
            if getattr(top, "_refresh_job", None) is not None:
                try:
                    top.after_cancel(top._refresh_job)
                except Exception:
                    pass
                top._refresh_job = None
            if top in self._plot_windows:
                self._plot_windows.remove(top)
            top.destroy()

        top.protocol("WM_DELETE_WINDOW", on_close_plot)
        refresh()

    # ===== loop principal =====
    def _tick(self):
        if self._closing:
            return
        self.clock_var.set(now().strftime("%Y-%m-%d %H:%M:%S"))
        for f in self.ferms:
            f.update_process()
        self._flow_tick()
        self._tick_job = self.after(1000, self._tick)

    def cerrar_todo_global(self):
        for f in self.ferms:
            f.stop_all()
        messagebox.showinfo("Seguridad", "Se cerraron todas las válvulas y se detuvo el control automático.")

    def export_all(self):
        for f in self.ferms:
            f.csv_export()

    def on_close(self):
        self._closing = True
        if self._tick_job is not None:
            try:
                self.after_cancel(self._tick_job)
            except Exception:
                pass
            self._tick_job = None

        for top in list(self._plot_windows):
            if top.winfo_exists():
                if getattr(top, "_refresh_job", None) is not None:
                    try:
                        top.after_cancel(top._refresh_job)
                    except Exception:
                        pass
                    top._refresh_job = None
                try:
                    top.destroy()
                except Exception:
                    pass
        self._plot_windows.clear()
        self._flow_plot_windows.clear()

        try:
            for f in self.ferms:
                f.stop_all()
            for reader in self.flow_readers.values():
                try:
                    reader.close()
                except Exception:
                    pass
            self.hw.cleanup()
        finally:
            try:
                for job in self.after_info():
                    try:
                        self.after_cancel(job)
                    except Exception:
                        pass
            except Exception:
                pass
            try:
                self.quit()
            except Exception:
                pass
            self.destroy()


if __name__ == "__main__":
    app = App()
    app.mainloop()
