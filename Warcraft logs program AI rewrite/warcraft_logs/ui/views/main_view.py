"""Tkinter view definitions for the raid analysis tool."""
from __future__ import annotations

import logging
import json
from pathlib import Path
from typing import Sequence

import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.collections import LineCollection
import numpy as np
import pandas as pd
import seaborn as sns
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

from PIL import Image

try:  # pragma: no cover - optional dependency for drag and drop support
    from tkinterdnd2 import DND_FILES, TkinterDnD
except Exception:  # pragma: no cover - fallback when tkinterdnd2 is unavailable
    TkinterDnD = tk
    DND_FILES = "DND_Files"

from ...config import AppConfig
from ..controller import RaidAnalysisController

LOGGER = logging.getLogger(__name__)

PLOT_TYPES = {
    "Scatter": "scatter",
    "Hexbin": "hexbin",
    "KDE": "kde",
    "Movement": "movement",
}


class RaidAnalysisApp(TkinterDnD.Tk):  # type: ignore[misc]
    """Root Tk application window."""

    def __init__(self, controller: RaidAnalysisController, config: AppConfig) -> None:
        super().__init__()
        self._controller = controller
        self._config = config
        self.title(config.ui.window_title)
        self.geometry("1400x900")
        self.configure(bg="#20232A")

        self._map_original: Image.Image | None = None
        self._map_image: np.ndarray | None = None
        self._map_extent: tuple[float, float, float, float] | None = None
        self._map_file: Path | None = None
        self._map_scale = tk.DoubleVar(value=1.0)
        self._map_offset_x = tk.DoubleVar(value=0.0)
        self._map_offset_y = tk.DoubleVar(value=0.0)
        self._map_rotation = tk.DoubleVar(value=0.0)
        self._map_scale.trace_add("write", self._on_map_transform_changed)
        self._map_offset_x.trace_add("write", self._on_map_transform_changed)
        self._map_offset_y.trace_add("write", self._on_map_transform_changed)
        self._map_rotation.trace_add("write", self._on_map_transform_changed)

        self._figure = plt.Figure(figsize=(10, 8))
        self._axes = self._figure.add_subplot(111)
        self._canvas = FigureCanvasTkAgg(self._figure, master=self)
        self._toolbar = NavigationToolbar2Tk(self._canvas, self)
        self._toolbar.update()
        self._canvas.get_tk_widget().pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self._build_sidebar()
        self._register_drag_and_drop()

    # Sidebar construction -------------------------------------------------
    def _build_sidebar(self) -> None:
        sidebar = ttk.Frame(self, padding=10)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)

        load_button = ttk.Button(sidebar, text="Open Combat Log", command=self._choose_log)
        load_button.pack(fill=tk.X, pady=5)

        ttk.Label(sidebar, text="Plot Type", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(15, 0))
        default_plot_label = next(
            (label for label, key in PLOT_TYPES.items() if key == self._config.visualization.default_plot),
            "Scatter",
        )
        self._plot_type = tk.StringVar(value=default_plot_label)
        plot_combo = ttk.Combobox(sidebar, textvariable=self._plot_type, state="readonly")
        plot_combo["values"] = list(PLOT_TYPES.keys())
        plot_combo.pack(fill=tk.X, pady=2)
        plot_combo.bind("<<ComboboxSelected>>", lambda _: self._redraw_plot())

        self._encounter_combo = self._create_encounter_combobox(sidebar)
        self._encounter_combo.bind("<<ComboboxSelected>>", lambda _: self._on_encounter_change())

        self._unit_list = self._create_multiselect_list(sidebar, "Units")
        self._spell_list = self._create_multiselect_list(sidebar, "Spells")
        self._event_list = self._create_multiselect_list(sidebar, "Event Types")

        ttk.Label(sidebar, text="Death Threshold", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(15, 0))
        self._death_threshold = tk.IntVar()
        death_entry = ttk.Spinbox(sidebar, from_=0, to=self._config.processing.max_death_threshold, textvariable=self._death_threshold, width=5)
        death_entry.pack(anchor=tk.W, pady=2)
        death_entry.bind("<FocusOut>", lambda _: self._apply_filters())

        ttk.Label(sidebar, text="Time Window (s)", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(15, 0))
        window_frame = ttk.Frame(sidebar)
        window_frame.pack(fill=tk.X, pady=2)
        self._time_start = tk.DoubleVar(value=0.0)
        self._time_end = tk.DoubleVar(value=60.0)
        ttk.Entry(window_frame, textvariable=self._time_start, width=7).pack(side=tk.LEFT)
        ttk.Entry(window_frame, textvariable=self._time_end, width=7).pack(side=tk.LEFT, padx=4)
        ttk.Button(window_frame, text="Apply", command=self._apply_filters).pack(side=tk.LEFT)

        ttk.Label(sidebar, text="Map Controls", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(20, 0))
        map_frame = ttk.Frame(sidebar)
        map_frame.pack(fill=tk.X, pady=2)
        ttk.Label(map_frame, text="Scale:").grid(row=0, column=0, sticky=tk.W)
        ttk.Spinbox(map_frame, from_=0.1, to=5.0, increment=0.1, textvariable=self._map_scale, width=6).grid(row=0, column=1, sticky=tk.W, padx=(4, 0))
        ttk.Label(map_frame, text="Offset X:").grid(row=1, column=0, sticky=tk.W)
        ttk.Entry(map_frame, textvariable=self._map_offset_x, width=8).grid(row=1, column=1, sticky=tk.W, padx=(4, 0))
        ttk.Label(map_frame, text="Offset Y:").grid(row=2, column=0, sticky=tk.W)
        ttk.Entry(map_frame, textvariable=self._map_offset_y, width=8).grid(row=2, column=1, sticky=tk.W, padx=(4, 0))
        ttk.Label(map_frame, text="Rotation:").grid(row=3, column=0, sticky=tk.W)
        ttk.Spinbox(map_frame, from_=-180.0, to=180.0, increment=5.0, textvariable=self._map_rotation, width=6).grid(row=3, column=1, sticky=tk.W, padx=(4, 0))

        button_frame = ttk.Frame(sidebar)
        button_frame.pack(fill=tk.X, pady=(10, 0))
        ttk.Button(button_frame, text="Save Calibration", command=self._save_calibration).pack(fill=tk.X, pady=2)
        ttk.Button(button_frame, text="Load Calibration", command=self._load_calibration).pack(fill=tk.X, pady=2)

    def _create_encounter_combobox(self, parent: ttk.Frame) -> ttk.Combobox:
        ttk.Label(parent, text="Encounter", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(15, 0))
        combo = ttk.Combobox(parent, state="readonly")
        combo.pack(fill=tk.X, pady=2)
        return combo

    def _create_multiselect_list(self, parent: ttk.Frame, label: str) -> tk.Listbox:
        ttk.Label(parent, text=label, font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, pady=(15, 0))
        listbox = tk.Listbox(parent, selectmode=tk.MULTIPLE, height=6, exportselection=False)
        listbox.pack(fill=tk.X, pady=2)
        listbox.bind("<<ListboxSelect>>", lambda _: self._apply_filters())
        return listbox

    # Drag and drop --------------------------------------------------------
    def _register_drag_and_drop(self) -> None:
        try:
            self.drop_target_register(DND_FILES)
            self.dnd_bind("<<Drop>>", self._handle_drop)
        except Exception as exc:  # pragma: no cover - drag and drop not available
            LOGGER.warning("Drag and drop unavailable: %s", exc)

    def _handle_drop(self, event) -> None:  # pragma: no cover - depends on TkinterDnD runtime
        path = Path(event.data.strip())
        if path.suffix.lower() == ".txt":
            self._open_log(path)
        elif path.suffix.lower() in {".png", ".jpg", ".jpeg"}:
            self._load_map(path)

    # File operations ------------------------------------------------------
    def _choose_log(self) -> None:
        path = filedialog.askopenfilename(title="Select Combat Log", filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")])
        if not path:
            return
        self._open_log(Path(path))

    def _open_log(self, path: Path) -> None:
        try:
            self._controller.load_log(path)
        except Exception as exc:
            LOGGER.exception("Failed to load combat log")
            messagebox.showerror("Error", f"Failed to load combat log: {exc}")
            return
        self._populate_filters()
        self._redraw_plot()

    def _load_map(self, path: Path) -> None:
        try:
            image = Image.open(path).convert("RGBA")
        except Exception as exc:  # pragma: no cover - runtime file errors
            LOGGER.exception("Failed to load map image")
            messagebox.showerror("Error", f"Failed to load map image: {exc}")
            return
        self._map_original = image
        self._map_file = path
        self._render_map_image()
        self._redraw_plot()

    def _render_map_image(self) -> None:
        if self._map_original is None:
            return
        rotated = self._map_original.rotate(-float(self._map_rotation.get()), expand=True)
        self._map_image = np.array(rotated)
        width, height = rotated.size
        scale = float(self._map_scale.get())
        offset_x = float(self._map_offset_x.get())
        offset_y = float(self._map_offset_y.get())
        half_width = (width * scale) / 2.0
        half_height = (height * scale) / 2.0
        self._map_extent = (
            offset_x - half_width,
            offset_x + half_width,
            offset_y - half_height,
            offset_y + half_height,
        )

    def _on_map_transform_changed(self, *_args) -> None:
        if self._map_original is None:
            return
        self._render_map_image()
        self._redraw_plot()

    # Filter handling ------------------------------------------------------
    def _populate_filters(self) -> None:
        state = self._controller.state
        filter_state = state.filter_state

        self._set_combobox_values(self._encounter_combo, [str(i) for i in filter_state.encounter_ids])
        units = [f"{(name or identifier)} ({identifier})" for identifier, name in self._controller.get_available_units()]
        self._populate_listbox(self._unit_list, units)
        spells = [f"{(name or identifier)} ({identifier})" for identifier, name in self._controller.get_available_spells()]
        self._populate_listbox(self._spell_list, spells)
        self._populate_listbox(self._event_list, list(filter_state.event_types))

    @staticmethod
    def _set_combobox_values(combo: ttk.Combobox, values: Sequence[str]) -> None:
        combo["values"] = values
        if values:
            combo.current(0)

    def _on_encounter_change(self) -> None:
        selection = self._encounter_combo.get()
        encounter_id = int(selection) if selection else None
        self._controller.apply_filters(encounter=encounter_id)
        self._redraw_plot()

    def _apply_filters(self) -> None:
        encounter_selection = self._encounter_combo.get()
        encounter_id = int(encounter_selection) if encounter_selection else None

        unit_selection = self._selection_from_listbox(self._unit_list)
        spell_selection = self._selection_from_listbox(self._spell_list)
        event_selection = self._selection_from_listbox(self._event_list)

        try:
            time_range = (float(self._time_start.get()), float(self._time_end.get()))
        except (TypeError, ValueError):
            time_range = None

        try:
            death_threshold = int(self._death_threshold.get())
        except (TypeError, ValueError):
            death_threshold = None

        selected_spell_ids = []
        for raw_value in spell_selection:
            if "(" not in raw_value:
                continue
            identifier = raw_value.split("(")[-1].rstrip(") ")
            try:
                selected_spell_ids.append(int(identifier))
            except ValueError:
                continue

        selected_unit_ids = []
        for raw_value in unit_selection:
            if "(" not in raw_value:
                continue
            selected_unit_ids.append(raw_value.split("(")[-1].rstrip(") "))

        self._controller.apply_filters(
            encounter=encounter_id,
            units=selected_unit_ids,
            spells=selected_spell_ids,
            event_types=event_selection,
            death_threshold=death_threshold,
            time_range=time_range,
        )
        self._redraw_plot()

    @staticmethod
    def _populate_listbox(listbox: tk.Listbox, values: Sequence[str]) -> None:
        listbox.delete(0, tk.END)
        for value in values:
            listbox.insert(tk.END, value)
        if values:
            listbox.selection_set(0, tk.END)

    @staticmethod
    def _selection_from_listbox(listbox: tk.Listbox) -> Sequence[str]:
        return tuple(listbox.get(index) for index in listbox.curselection())

    # Visualisation --------------------------------------------------------
    def _redraw_plot(self) -> None:
        if self._controller.state.normalised_log is None:
            return
        plot_type = PLOT_TYPES.get(self._plot_type.get(), self._config.visualization.default_plot)
        data = self._controller.apply_filters()
        self._axes.clear()

        if self._map_image is not None and self._map_extent is not None:
            self._axes.imshow(self._map_image, extent=self._map_extent, origin="lower", alpha=0.6)

        if data.empty:
            self._axes.text(0.5, 0.5, "No data to display", ha="center", va="center", color="white")
            self._canvas.draw_idle()
            return

        if plot_type == "scatter":
            self._draw_scatter(data)
        elif plot_type == "hexbin":
            self._draw_hexbin(data)
        elif plot_type == "kde":
            self._draw_kde(data)
        else:
            self._draw_movement(data)

        self._axes.set_xlabel("X")
        self._axes.set_ylabel("Y")
        self._axes.set_facecolor("#1E1E24")
        self._figure.tight_layout()
        self._canvas.draw_idle()

    def _draw_scatter(self, frame: pd.DataFrame) -> None:
        scatter = self._axes.scatter(frame["x"], frame["y"], c=frame["relative_time"], cmap=self._config.visualization.colormap, s=15)
        self._figure.colorbar(scatter, ax=self._axes, label="Seconds")

    def _draw_hexbin(self, frame: pd.DataFrame) -> None:
        hb = self._axes.hexbin(
            frame["x"],
            frame["y"],
            C=frame["amount"],
            gridsize=self._config.visualization.hexbin_grid_size,
            cmap=self._config.visualization.colormap,
            reduce_C_function=np.mean,
        )
        self._figure.colorbar(hb, ax=self._axes, label="Mean Amount")

    def _draw_kde(self, frame: pd.DataFrame) -> None:
        sns.kdeplot(
            data=frame.dropna(subset=["x", "y"]),
            x="x",
            y="y",
            fill=True,
            ax=self._axes,
            cmap=self._config.visualization.colormap,
            bw_adjust=self._config.visualization.kde_bandwidth,
            thresh=0.05,
        )

    def _draw_movement(self, frame: pd.DataFrame) -> None:
        groups = frame.groupby("source_id")
        for _, group in groups:
            group = group.sort_values("relative_time")
            points = group[["x", "y"]].to_numpy(dtype=float)
            if len(points) < 2:
                continue
            segments = np.concatenate([points[:-1, None, :], points[1:, None, :]], axis=1)
            lc = LineCollection(
                segments,
                cmap=self._config.visualization.colormap,
                norm=plt.Normalize(group["relative_time"].min(), group["relative_time"].max()),
            )
            lc.set_array(group["relative_time"].to_numpy(dtype=float))
            lc.set_linewidth(2)
            self._axes.add_collection(lc)
            self._axes.scatter(points[0, 0], points[0, 1], marker="o", color="white", s=40)
            self._axes.scatter(points[-1, 0], points[-1, 1], marker="x", color="white", s=40)

        self._axes.autoscale_view()

    # Map calibration persistence ------------------------------------------
    def _save_calibration(self) -> None:
        if self._map_file is None:
            messagebox.showinfo("Calibration", "Load a map image before saving calibration settings.")
            return
        path = filedialog.asksaveasfilename(
            title="Save Map Calibration",
            filetypes=[("JSON", "*.json"), ("All Files", "*.*")],
            defaultextension=".json",
        )
        if not path:
            return
        payload = {
            "map_file": str(self._map_file),
            "scale": float(self._map_scale.get()),
            "offset_x": float(self._map_offset_x.get()),
            "offset_y": float(self._map_offset_y.get()),
            "rotation": float(self._map_rotation.get()),
        }
        try:
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(payload, handle, indent=2)
        except OSError as exc:
            messagebox.showerror("Calibration", f"Failed to save calibration: {exc}")

    def _load_calibration(self) -> None:
        path = filedialog.askopenfilename(
            title="Load Map Calibration",
            filetypes=[("JSON", "*.json"), ("All Files", "*.*")],
        )
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                payload = json.load(handle)
        except (OSError, json.JSONDecodeError) as exc:
            messagebox.showerror("Calibration", f"Failed to load calibration: {exc}")
            return

        self._map_scale.set(payload.get("scale", 1.0))
        self._map_offset_x.set(payload.get("offset_x", 0.0))
        self._map_offset_y.set(payload.get("offset_y", 0.0))
        self._map_rotation.set(payload.get("rotation", 0.0))

        map_file = payload.get("map_file")
        if map_file:
            map_path = Path(map_file)
            if map_path.exists():
                self._load_map(map_path)
            else:
                messagebox.showwarning("Calibration", f"Map file not found: {map_file}")


__all__ = ["RaidAnalysisApp"]
