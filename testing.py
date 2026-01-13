import datetime as dt
import math
import os
import sys
import tkinter as tk
from tkinter import ttk
from importlib import util as importlib_util


# =========================
# Configuracion basica
# =========================
SIMULADOR = os.environ.get("SIMULADOR", "").strip().lower() in {"1", "true", "yes"}


def parse_int(value: str, default: int) -> int:
    raw = (value or "").strip().lower()
    if not raw:
        return default
    if raw.startswith("0x"):
        return int(raw, 16)
    return int(raw, 10)


ADS1115_ADDR = parse_int(os.environ.get("ADS1115_ADDR", "0x48"), 0x48)
ADS1115_CH = parse_int(os.environ.get("ADS1115_CH", "0"), 0)
ADS1115_GAIN = parse_int(os.environ.get("ADS1115_GAIN", "1"), 1)

SHUNT_OHMS = float(os.environ.get("SHUNT_OHMS", "200.0"))
FLOW_MIN_M3H = float(os.environ.get("FLOW_MIN_M3H", "0.0"))
FLOW_MAX_M3H = float(os.environ.get("FLOW_MAX_M3H", "100.0"))

SAMPLE_PERIOD_SEC_ENV = os.environ.get("SAMPLE_PERIOD_SEC", "").strip()
SAMPLE_PERIOD_SEC = parse_int(SAMPLE_PERIOD_SEC_ENV, 0) if SAMPLE_PERIOD_SEC_ENV else None
PLOT_WINDOW_ENV = os.environ.get("PLOT_WINDOW_HOURS", "").strip()
PLOT_WINDOW_HOURS = float(PLOT_WINDOW_ENV) if PLOT_WINDOW_ENV else 0.0


def now():
    return dt.datetime.now()


def voltage_to_current_ma(voltage: float, shunt_ohms: float) -> float:
    return (voltage / shunt_ohms) * 1000.0


def current_to_flow_m3h(current_ma: float) -> float:
    if FLOW_MAX_M3H <= FLOW_MIN_M3H:
        return 0.0
    current_ma = max(4.0, min(20.0, current_ma))
    span = 16.0
    return FLOW_MIN_M3H + (current_ma - 4.0) * (FLOW_MAX_M3H - FLOW_MIN_M3H) / span


class ADS1115Reader:
    def __init__(self, address: int, channel: int, gain: int):
        self.address = address
        self.channel = max(0, min(3, channel))
        self.gain = gain
        self.sim = SIMULADOR
        self.sim_reason = ""
        self._sim_phase = 0.0
        self._ads = None
        self._chan = None
        self._init_hw()

    def _init_hw(self):
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

        i2c = busio.I2C(board.SCL, board.SDA)
        ads = ADS.ADS1115(i2c, address=self.address)
        ads.gain = self.gain
        ch_map = [ADS.P0, ADS.P1, ADS.P2, ADS.P3]
        self._ads = ads
        self._chan = AnalogIn(ads, ch_map[self.channel])

    def read_voltage(self) -> float:
        if self.sim or not self._chan:
            self._sim_phase = (self._sim_phase + 0.15) % (2 * math.pi)
            current_ma = 12.0 + 8.0 * math.sin(self._sim_phase)
            return (current_ma / 1000.0) * SHUNT_OHMS
        return float(self._chan.voltage)


class FlowApp(tk.Tk):
    def __init__(self, reader: ADS1115Reader):
        super().__init__()
        self.reader = reader
        self.samples = []
        self.next_sample = None
        self._after_job = None
        self._closing = False
        if SAMPLE_PERIOD_SEC is None:
            self.sample_period_sec = 10 if reader.sim else 600
        else:
            self.sample_period_sec = SAMPLE_PERIOD_SEC
        self.title("Caudalimetro CO2 - 4-20 mA")
        self.geometry("950x620")
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        header = ttk.Frame(self, padding=8)
        header.pack(fill="x")
        ttk.Label(header, text="Caudalimetro CO2", font=("Segoe UI", 16, "bold")).pack(side="left")

        sim_text = "SIMULADOR" if reader.sim else "HARDWARE"
        sim_color = "#dc2626" if reader.sim else "#16a34a"
        self.sim_label = ttk.Label(header, text=sim_text, foreground=sim_color)
        self.sim_label.pack(side="right")

        stats = ttk.Frame(self, padding=8)
        stats.pack(fill="x")

        self.flow_var = tk.StringVar(value="0.00 m3/h")
        self.current_var = tk.StringVar(value="0.00 mA")
        self.voltage_var = tk.StringVar(value="0.000 V")
        self.status_var = tk.StringVar(value="Esperando...")
        self.next_var = tk.StringVar(value="--:--:--")

        ttk.Label(stats, text="Caudal:", font=("Segoe UI", 12, "bold")).grid(row=0, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.flow_var, font=("Segoe UI", 12)).grid(row=0, column=1, sticky="w")
        ttk.Label(stats, text="Corriente:", font=("Segoe UI", 12, "bold")).grid(row=1, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.current_var, font=("Segoe UI", 12)).grid(row=1, column=1, sticky="w")
        ttk.Label(stats, text="Voltaje:", font=("Segoe UI", 12, "bold")).grid(row=2, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.voltage_var, font=("Segoe UI", 12)).grid(row=2, column=1, sticky="w")
        ttk.Label(stats, text="Estado:", font=("Segoe UI", 12, "bold")).grid(row=3, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.status_var, font=("Segoe UI", 12)).grid(row=3, column=1, sticky="w")
        ttk.Label(stats, text="Siguiente muestra:", font=("Segoe UI", 12, "bold")).grid(row=4, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.next_var, font=("Segoe UI", 12)).grid(row=4, column=1, sticky="w")

        for col in range(2):
            stats.grid_columnconfigure(col, weight=1)

        plot_frame = ttk.Frame(self, padding=8)
        plot_frame.pack(fill="both", expand=True)

        self._init_plot(plot_frame)
        self._schedule_loop()

    def _init_plot(self, parent):
        import matplotlib

        matplotlib.use("TkAgg")
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        import matplotlib.pyplot as plt  # type: ignore

        self._mdates = mdates
        self._fig, self._ax = plt.subplots(figsize=(9, 4), dpi=100)
        self._line, = self._ax.plot([], [], color="#2563eb", linewidth=2)
        self._ax.set_title("Caudal CO2 (m3/h)")
        self._ax.set_ylabel("m3/h")
        self._ax.set_xlabel("Hora")
        self._ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M"))
        self._ax.grid(True, alpha=0.2)

        self._canvas = FigureCanvasTkAgg(self._fig, master=parent)
        self._canvas.get_tk_widget().pack(fill="both", expand=True)

    def _schedule_loop(self):
        if self._closing or not self.winfo_exists():
            return
        if self.next_sample is None or now() >= self.next_sample:
            self._take_sample()
        self._update_countdown()
        self._after_job = self.after(1000, self._schedule_loop)

    def _on_close(self):
        self._closing = True
        if self._after_job is not None:
            try:
                self.after_cancel(self._after_job)
            except Exception:
                pass
            self._after_job = None
        try:
            self.quit()
        except Exception:
            pass
        self.destroy()

    def _update_countdown(self):
        if self.next_sample is None:
            self.next_var.set("--:--:--")
            return
        delta = self.next_sample - now()
        if delta.total_seconds() < 0:
            self.next_var.set("00:00:00")
        else:
            total = int(delta.total_seconds())
            hh = total // 3600
            mm = (total % 3600) // 60
            ss = total % 60
            self.next_var.set(f"{hh:02d}:{mm:02d}:{ss:02d}")

    def _take_sample(self):
        ts = now()
        voltage = self.reader.read_voltage()
        current_ma = voltage_to_current_ma(voltage, SHUNT_OHMS)
        flow = current_to_flow_m3h(current_ma)

        status = "OK"
        if current_ma < 3.8:
            status = "Bajo rango"
        elif current_ma > 20.5:
            status = "Alto rango"

        self.samples.append((ts, flow))
        self._prune_samples()
        self._update_plot()

        self.flow_var.set(f"{flow:0.2f} m3/h")
        self.current_var.set(f"{current_ma:0.2f} mA")
        self.voltage_var.set(f"{voltage:0.3f} V")
        self.status_var.set(status)

        self.next_sample = ts + dt.timedelta(seconds=self.sample_period_sec)

    def _prune_samples(self):
        if not self.samples:
            return
        if PLOT_WINDOW_HOURS <= 0:
            return
        cutoff = now() - dt.timedelta(hours=PLOT_WINDOW_HOURS)
        self.samples = [(ts, val) for ts, val in self.samples if ts >= cutoff]

    def _update_plot(self):
        if not self.samples:
            return
        times = [ts for ts, _ in self.samples]
        values = [val for _, val in self.samples]
        self._line.set_data(times, values)

        right = times[-1]
        if PLOT_WINDOW_HOURS <= 0:
            left = times[0]
        else:
            left = right - dt.timedelta(hours=PLOT_WINDOW_HOURS)
        self._ax.set_xlim(left, right)

        vmin = min(values)
        vmax = max(values)
        pad = (vmax - vmin) * 0.1 if vmax != vmin else 1.0
        self._ax.set_ylim(vmin - pad, vmax + pad)
        self._fig.autofmt_xdate()
        self._canvas.draw_idle()


def main():
    if not importlib_util.find_spec("matplotlib"):
        print("Falta matplotlib. Instala con: pip install matplotlib")
        sys.exit(1)

    reader = ADS1115Reader(ADS1115_ADDR, ADS1115_CH, ADS1115_GAIN)
    if reader.sim:
        print(f"[INFO] Modo simulador activo. {reader.sim_reason}")
    else:
        print(f"[INFO] ADS1115 activo en direccion 0x{ADS1115_ADDR:02X}, canal A{ADS1115_CH}")

    app = FlowApp(reader)
    try:
        app.mainloop()
    except KeyboardInterrupt:
        pass
    finally:
        try:
            app.destroy()
        except Exception:
            pass


if __name__ == "__main__":
    main()
