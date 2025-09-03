import tkinter as tk
from tkinter import ttk, simpledialog, filedialog, colorchooser, scrolledtext
import pyautogui
import time
import threading
import json
import os
import random
import shutil
from PIL import Image, ImageTk, ImageGrab # Pillow for pixel color and image ops
import platform
import logging
from logging.handlers import RotatingFileHandler
import uuid
import queue
import math

# --- Global Variables & Constants ---
DEFAULT_PROJECT_NAME = "UntitledSequence"

# Special keys for PyAutoGUI keyboard actions
PYAUTOGUI_SPECIAL_KEYS = sorted([
    'accept', 'add', 'alt', 'altleft', 'altright', 'apps', 'backspace',
    'browserback', 'browserfavorites', 'browserforward', 'browserhome',
    'browserrefresh', 'browsersearch', 'browserstop', 'capslock', 'clear',
    'convert', 'ctrl', 'ctrlleft', 'ctrlright', 'decimal', 'del', 'delete',
    'divide', 'down', 'end', 'enter', 'esc', 'escape', 'execute', 'f1', 'f2',
    'f3', 'f4', 'f5', 'f6', 'f7', 'f8', 'f9', 'f10', 'f11', 'f12', 'f13',
    'f14', 'f15', 'f16', 'f17', 'f18', 'f19', 'f20', 'f21', 'f22', 'f23',
    'f24', 'final', 'fn', 'hanguel', 'hanja', 'help', 'home', 'insert', 'junja',
    'kana', 'kanji', 'launchapp1', 'launchapp2', 'launchmail',
    'launchmediaselect', 'left', 'modechange', 'multiply', 'nexttrack',
    'nonconvert', 'num0', 'num1', 'num2', 'num3', 'num4', 'num5', 'num6',
    'num7', 'num8', 'num9', 'numlock', 'pagedown', 'pageup', 'pause', 'pgdn',
    'pgup', 'playpause', 'prevtrack', 'print', 'printscreen', 'prntscrn',
    'prtscr', 'return', 'right', 'scrolllock', 'select', 'separator', 'shift',
    'shiftleft', 'shiftright', 'sleep', 'space', 'stop', 'subtract', 'tab',
    'up', 'volumedown', 'volumemute', 'volumeup', 'win', 'winleft', 'winright', 'yen'
])

# Predefined hotkeys for the Hotkey Combo action
PREDEFINED_HOTKEYS = {
    # System & Navigation
    "Switch Apps (Alt+Tab)": ['alt', 'tab'],
    "Close Window (Alt+F4)": ['alt', 'f4'],
    "Show Desktop (Win+D)": ['win', 'd'],
    "Open File Explorer (Win+E)": ['win', 'e'],
    "Open Run Dialog (Win+R)": ['win', 'r'],

    # File & Window Management
    "Copy (Ctrl+C)": ['ctrl', 'c'],
    "Cut (Ctrl+X)": ['ctrl', 'x'],
    "Paste (Ctrl+V)": ['ctrl', 'v'],
    "Undo (Ctrl+Z)": ['ctrl', 'z'],
    "Redo (Ctrl+Y)": ['ctrl', 'y'],
    "Select All (Ctrl+A)": ['ctrl', 'a'],
    "New Window (Ctrl+N)": ['ctrl', 'n'],
    "New Folder (Ctrl+Shift+N)": ['ctrl', 'shift', 'n'],
    "Properties (Alt+Enter)": ['alt', 'enter'],

    # Browser Shortcuts
    "New Tab (Ctrl+T)": ['ctrl', 't'],
    "Close Tab (Ctrl+W)": ['ctrl', 'w'],
    "Reopen Closed Tab (Ctrl+Shift+T)": ['ctrl', 'shift', 't'],
    "Next Tab (Ctrl+Tab)": ['ctrl', 'tab'],
    "Previous Tab (Ctrl+Shift+Tab)": ['ctrl', 'shift', 'tab'],
    "Focus Address Bar (Ctrl+L)": ['ctrl', 'l'],

    # Text Editing
    "Move Cursor Word Left (Ctrl+Left)": ['ctrl', 'left'],
    "Move Cursor Word Right (Ctrl+Right)": ['ctrl', 'right'],
    "Delete Previous Word (Ctrl+Backspace)": ['ctrl', 'backspace'],
    "Select Word Left (Ctrl+Shift+Left)": ['ctrl', 'shift', 'left'],
    "Select Word Right (Ctrl+Shift+Right)": ['ctrl', 'shift', 'right'],
    "Jump to Start of Doc (Ctrl+Home)": ['ctrl', 'home'],
    "Jump to End of Doc (Ctrl+End)": ['ctrl', 'end'],
}
PREDEFINED_HOTKEY_NAMES = sorted(PREDEFINED_HOTKEYS.keys())

# --- Helper Functions ---
def get_screen_center_for_window(window_width, window_height, root):
    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()
    x = (screen_width // 2) - (window_width // 2)
    y = (screen_height // 2) - (window_height // 2)
    return x, y

# --- Main Application Class ---
class DesktopAutomationApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Python Desktop Automation Tool")
        x, y = get_screen_center_for_window(550, 700, root)
        self.root.geometry(f"+{x}+{y}")

        # Theme state and menu
        self._theme_mode = 'dark'  # default preference
        self._setup_logging()
        self._apply_system_theme()
        self._setup_menubar()

        self.objects = {}
        self.current_steps = []
        self.current_project_path = None
        self.current_sequence_name = DEFAULT_PROJECT_NAME
        self.loop_count = tk.IntVar(value=1)
        self.sequence_modified = False

        self.grid_window = None
        # Baseline cell size ~50x50px => rows/cols from screen size
        _sw, _sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.grid_rows_var = tk.IntVar(value=50)
        self.grid_cols_var = tk.IntVar(value=50)
        self.selected_grid_cells = []

        self.drag_select_window = None
        self.drag_start_x = None
        self.drag_start_y = None
        self.drag_rect_id = None

        self.pixel_monitor_active = False
        self._pixel_listener = None

        self.container = tk.Frame(root)
        self.container.pack(fill="both", expand=True)
        # Make the grid inside container expand with the window
        self.container.grid_rowconfigure(0, weight=1)
        self.container.grid_columnconfigure(0, weight=1)

        self.frames = {}
        # Track any extra ObjectCreationFrame instances opened in new windows
        self._aux_object_frames = []
        # Track whether we've already maximized Step Creator once
        self._step_creator_maximized_once = False
        for F in (MainFrame, ObjectCreationFrame, StepCreatorFrame, InstructionsFrame):
            page_name = F.__name__
            frame = F(parent=self.container, controller=self)
            self.frames[page_name] = frame
            frame.grid(row=0, column=0, sticky="nsew")

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.show_frame("MainFrame")

    def _refresh_all_object_views(self):
        try:
            oc = self.frames.get("ObjectCreationFrame")
            if oc and oc.winfo_exists():
                oc.update_objects_display()
            for fr in list(self._aux_object_frames):
                try:
                    if fr and fr.winfo_exists():
                        fr.update_objects_display()
                except Exception:
                    pass
        except Exception:
            if hasattr(self, 'logger'):
                self.logger.exception('Refresh object views failed')


    # --- Logging & Toasts ---
    def _setup_logging(self):
        try:
            logs_dir = os.path.join(os.getcwd(), 'logs')
            os.makedirs(logs_dir, exist_ok=True)
            self.logger = logging.getLogger('automation_maker')
            self.logger.setLevel(logging.INFO)
            handler = RotatingFileHandler(os.path.join(logs_dir, 'automation.log'), maxBytes=1_000_000, backupCount=5)
            fmt = logging.Formatter('%(asctime)s %(levelname)s %(message)s')
            handler.setFormatter(fmt)
            if not any(isinstance(h, RotatingFileHandler) for h in self.logger.handlers):
                self.logger.addHandler(handler)
        except Exception as e:
            print('Logging setup failed:', e)

    def show_toast(self, message, duration_ms=3500):
        try:
            tw = tk.Toplevel(self.root)
            tw.wm_overrideredirect(True)
            tw.attributes('-topmost', True)
            pad = 8
            bg = '#333333'; fg = '#ffffff'
            fr = tk.Frame(tw, bg=bg)
            fr.pack(fill='both', expand=True)
            tk.Label(fr, text=message, bg=bg, fg=fg, padx=pad, pady=pad).pack()
            self.root.update_idletasks()
            # bottom-right corner
            x = self.root.winfo_x() + self.root.winfo_width() - 320
            y = self.root.winfo_y() + self.root.winfo_height() - 80
            tw.geometry(f"300x50+{max(0,x)}+{max(0,y)}")
            tw.after(duration_ms, tw.destroy)
        except Exception as e:
            if hasattr(self, 'logger'):
                self.logger.exception('Toast failed: %s', e)

    def _setup_menubar(self):
        menu = tk.Menu(self.root)
        theme_menu = tk.Menu(menu, tearoff=0)
        theme_menu.add_command(label="Light", command=lambda: self.set_theme_mode('light'))
        theme_menu.add_command(label="Dark", command=lambda: self.set_theme_mode('dark'))
        theme_menu.add_command(label="Follow System", command=lambda: self.set_theme_mode('system'))
        menu.add_cascade(label="Theme", menu=theme_menu)

        window_menu = tk.Menu(menu, tearoff=0)
        window_menu.add_command(label="Open Object Creation (Window)", command=self.open_object_creation_window)
        window_menu.add_command(label="Open Step Creator (Window)", command=self.open_step_creator_window)
        window_menu.add_command(label="Open Sequence Looper (Window)", command=self.open_sequence_looper_window)
        menu.add_cascade(label="Window", menu=window_menu)
        self.root.config(menu=menu)

    def open_object_creation_window(self):
        try:
            win = tk.Toplevel(self.root)
            win.title("Object Creation")
            frame = ObjectCreationFrame(parent=win, controller=self)
            frame.pack(fill="both", expand=True)
            # Ensure newly opened window shows current objects
            self._aux_object_frames.append(frame)
            def _on_destroy(_e=None, fr=frame):
                try:
                    if fr in self._aux_object_frames:
                        self._aux_object_frames.remove(fr)
                except Exception:
                    pass
            win.bind('<Destroy>', _on_destroy)
            try:
                frame.update_objects_display()
            except Exception:
                pass
            win.lift(); win.focus_force()
        except Exception as e:
            code = str(uuid.uuid4())[:8]
            self.logger.exception("Object window error %s", code)
            self.show_toast(f"Error opening Object window (code {code})")

    def open_step_creator_window(self):
        try:
            win = tk.Toplevel(self.root)
            win.title("Step Creator")
            try:
                win.state('zoomed')
            except Exception:
                try:
                    win.attributes('-zoomed', True)
                except Exception:
                    pass
            frame = StepCreatorFrame(parent=win, controller=self)
            frame.pack(fill="both", expand=True)
            try:
                frame.clear_and_rebuild_steps(self.current_steps)
            except Exception:
                pass
            def _close():
                if self._check_unsaved_changes():
                    win.destroy()
            win.protocol("WM_DELETE_WINDOW", _close)
            win.lift(); win.focus_force()
        except Exception as e:
            code = str(uuid.uuid4())[:8]
            self.logger.exception("Step window error %s", code)
            self.show_toast(f"Error opening Step window (code {code})")

    def open_sequence_looper_window(self):
        win = tk.Toplevel(self.root)
        win.title("Sequence Looper")
        frm = ttk.Frame(win); frm.pack(fill="both", expand=True, padx=10, pady=10)

        cols = ("Name", "Path")
        tree = ttk.Treeview(frm, columns=cols, show='headings', height=8)
        for c in cols: tree.heading(c, text=c)
        tree.column("Name", width=220); tree.column("Path", width=420)
        tree.pack(fill="both", expand=True)

        btns = ttk.Frame(frm); btns.pack(fill="x", pady=6)
        def add_seq():
            path = filedialog.askopenfilename(title="Add Sequence File",defaultextension=".json",filetypes=[("JSON files","*.json"),("All files","*.*")],parent=win)
            if not path: return
            name = os.path.splitext(os.path.basename(path))[0]
            tree.insert('', 'end', values=(name, path))
        def remove_sel():
            for i in tree.selection(): tree.delete(i)
        # placeholder removed
        def move_up():
            sel = tree.selection()
            for iid in sel:
                prev = tree.prev(iid)
                if prev:
                    tree.move(iid, tree.parent(iid), tree.index(prev))
        def move_down():
            sel = list(tree.selection())[::-1]
            for iid in sel:
                nxt = tree.next(iid)
                if nxt:
                    tree.move(iid, tree.parent(iid), tree.index(nxt)+1)
        ttk.Button(btns, text="Add", command=add_seq).pack(side=tk.LEFT, padx=3)
        ttk.Button(btns, text="Remove", command=remove_sel).pack(side=tk.LEFT, padx=3)
        ttk.Button(btns, text="Up", command=move_up).pack(side=tk.LEFT, padx=3)
        ttk.Button(btns, text="Down", command=move_down).pack(side=tk.LEFT, padx=3)

        controls = ttk.Frame(frm); controls.pack(fill="x", pady=6)
        loop_forever = tk.BooleanVar(value=True)
        cycles_var = tk.IntVar(value=1)
        ttk.Checkbutton(controls, text="Loop forever", variable=loop_forever).pack(side=tk.LEFT)
        ttk.Label(controls, text="Cycles:").pack(side=tk.LEFT, padx=(10,2))
        cycles_spin = ttk.Spinbox(controls, from_=1, to=9999, textvariable=cycles_var, width=6)
        cycles_spin.pack(side=tk.LEFT)
        status_var = tk.StringVar(value="Idle")
        ttk.Label(controls, textvariable=status_var).pack(side=tk.RIGHT)

        stop_flag = {"stop": False}
        def start_loop():
            items = tree.get_children('')
            if not items: return
            stop_flag["stop"] = False
            total_cycles = 999999999 if loop_forever.get() else max(1, int(cycles_var.get() or 1))
            status_var.set("Running...")
            for cycle in range(total_cycles):
                if stop_flag["stop"]: break
                for iid in tree.get_children(''):
                    if stop_flag["stop"]: break
                    name, path = tree.item(iid, 'values')
                    status_var.set(f"Running: {name}")
                    win.update_idletasks()
                    try:
                        self._run_sequence_file_once(path)
                    except Exception as e:
                        print(f"Looper error for {path}: {e}")
            status_var.set("Stopped" if stop_flag["stop"] else "Finished")

        def stop_loop():
            stop_flag["stop"] = True

        actions = ttk.Frame(frm); actions.pack(fill="x", pady=6)
        ttk.Button(actions, text="Start", command=start_loop).pack(side=tk.LEFT, padx=5)
        ttk.Button(actions, text="Stop", command=stop_loop).pack(side=tk.LEFT, padx=5)

    def _run_sequence_file_once(self, filepath):
        # Save current state
        prev = {
            'objects': self.objects.copy(),
            'steps': list(self.current_steps),
            'project_path': self.current_project_path,
            'sequence_name': self.current_sequence_name,
            'loop_count': self.loop_count.get(),
        }
        try:
            with open(filepath, 'r') as f:
                data = json.load(f)
            self.current_project_path = os.path.dirname(filepath)
            self.current_sequence_name = data.get("sequence_name", os.path.splitext(os.path.basename(filepath))[0])
            # Rebuild objects resolving image paths
            new_objects = {}
            for obj_name, obj in data.get("objects", {}).items():
                o = obj.copy()
                if o.get("type") == "image" and o.get("image_path"):
                    rel = o["image_path"]
                    abs_p = os.path.join(self.current_project_path, rel)
                    if os.path.exists(abs_p): o["image_path"] = abs_p
                new_objects[obj_name] = o
            self.objects = new_objects
            self.current_steps = data.get("steps", [])
            self.loop_count.set(data.get("loop_count", 1))
            # Refresh UI and run
            self.frames["ObjectCreationFrame"].update_objects_display()
            self.frames["StepCreatorFrame"].clear_and_rebuild_steps(self.current_steps)
            self.run_sequence()
        finally:
            # Restore previous state
            self.objects = prev['objects']
            self.current_steps = prev['steps']
            self.current_project_path = prev['project_path']
            self.current_sequence_name = prev['sequence_name']
            self.loop_count.set(prev['loop_count'])
            self.frames["ObjectCreationFrame"].update_objects_display()
            self.frames["StepCreatorFrame"].clear_and_rebuild_steps(self.current_steps)

    def set_theme_mode(self, mode):
        self._theme_mode = mode
        self._apply_system_theme()
        # Update backgrounds that were hard-coded/derived
        for f in self.frames.values():
            try:
                if hasattr(f, 'refresh_content'):
                    f.refresh_content()
            except Exception:
                pass

    def _apply_system_theme(self):
        """Apply theme based on preference: 'light', 'dark', or 'system'.
        If sv_ttk is installed, use it for modern light/dark. Otherwise fall
        back to ttk themes and basic color adjustments.
        """
        try:
            style = ttk.Style(self.root)
            current_os = platform.system()
            available = set(style.theme_names())
            # Determine desired mode
            desired = self._theme_mode
            if desired == 'system':
                # Infer system preference on Windows; assume light elsewhere
                prefers_dark = False
                if current_os == 'Windows':
                    try:
                        import winreg  # type: ignore
                        key = winreg.OpenKey(
                            winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize"
                        )
                        value, _ = winreg.QueryValueEx(key, "AppsUseLightTheme")
                        prefers_dark = (int(value) == 0)
                    except Exception:
                        prefers_dark = False
                desired = 'dark' if prefers_dark else 'light'

            # If sv_ttk is available, use it
            try:
                import sv_ttk  # type: ignore
                if desired == 'dark': sv_ttk.set_theme('dark')
                else: sv_ttk.set_theme('light')
                return
            except Exception:
                pass

            # Fallback to builtin ttk themes
            if desired == 'dark':
                # Prefer 'clam' for reliable color overrides in dark mode
                base_candidates = ('clam', 'alt', 'default', 'vista', 'xpnative', 'winnative')
            else:
                if current_os == 'Windows':
                    base_candidates = ('vista', 'xpnative', 'winnative', 'clam', 'default')
                elif current_os == 'Darwin':
                    base_candidates = ('aqua', 'clam', 'default', 'alt')
                else:
                    base_candidates = ('clam', 'alt', 'default')
            for theme in base_candidates:
                if theme in available:
                    style.theme_use(theme)
                    break

            # Light/dark tweaks for ttk widgets if no sv_ttk
            if desired == 'dark':
                bg = '#2b2b2b'; fg = '#e6e6e6'; acc = '#3a3a3a'
                style.configure('.', background=bg, foreground=fg)
                style.configure('TFrame', background=bg)
                style.configure('TLabel', background=bg, foreground=fg)
                style.configure('TButton', background=acc, foreground=fg)
                style.map('TButton',
                           foreground=[('disabled', '#888888'), ('active', fg), ('pressed', fg)],
                           background=[('active', '#4a4a4a'), ('pressed', '#444444')])
                style.configure('TEntry', fieldbackground='#1f1f1f', foreground=fg)
                style.configure('TCombobox', fieldbackground='#1f1f1f', foreground=fg)
                style.map('TCombobox', fieldbackground=[('readonly', '#1f1f1f')], foreground=[('readonly', fg)])
                try:
                    self.root.configure(bg=bg)
                    # Basic defaults for classic tk widgets
                    self.root.option_add("*Background", bg)
                    self.root.option_add("*Foreground", fg)
                    self.root.option_add("*Entry.Background", '#1f1f1f')
                    self.root.option_add("*Entry.Foreground", fg)
                    self.root.option_add("*Text.Background", '#1f1f1f')
                    self.root.option_add("*Text.Foreground", fg)
                    self.root.option_add("*Listbox.Background", '#1f1f1f')
                    self.root.option_add("*Listbox.Foreground", fg)
                    self.root.option_add("*Button.Background", acc)
                    self.root.option_add("*Button.Foreground", fg)
                    self.root.option_add("*Button.activeBackground", '#4a4a4a')
                    self.root.option_add("*activeBackground", acc)
                    self.root.option_add("*selectBackground", '#555555')
                except Exception:
                    pass
            else:
                # Default light colors are fine; ensure root matches
                try:
                    self.root.configure(bg=style.lookup('TFrame', 'background') or '#F0F0F0')
                except Exception:
                    pass
        except Exception:
            # If anything goes wrong, stick with Tk's default theme
            pass

    def mark_sequence_modified(self, modified=True):
        self.sequence_modified = modified
        current_title = self.root.title()
        base_title = current_title.rstrip("*")
        
        active_frame_name = ""
        for name, frame_instance in self.frames.items():
            if frame_instance.winfo_ismapped():
                active_frame_name = name
                break
        
        new_title_base = active_frame_name if active_frame_name else base_title

        if modified:
            self.root.title(new_title_base + "*")
        else:
            self.root.title(new_title_base)

    def show_frame(self, page_name):
        frame = self.frames[page_name]
        frame.tkraise()
        if hasattr(frame, 'refresh_content') and callable(getattr(frame, 'refresh_content')):
            frame.refresh_content()
        if page_name == "StepCreatorFrame" and not self._step_creator_maximized_once:
            try:
                self.root.state('zoomed')
            except Exception:
                try:
                    self.root.attributes('-zoomed', True)
                except Exception:
                    pass
            self._step_creator_maximized_once = True

        title_base = page_name
        if self.sequence_modified:
            self.root.title(title_base + "*")
        else:
            self.root.title(title_base)

        self.root.update_idletasks()
        self.root.geometry("")

    def get_object_names(self, object_type=None):
        if object_type:
            return [name for name, obj_data in self.objects.items() if obj_data.get("type") == object_type]
        return list(self.objects.keys())

    def add_object(self, name, obj_data):
        if name in self.objects:
            simpledialog.messagebox.showwarning("Warning", f"Object with name '{name}' already exists. Please choose a unique name.")
            return False
        if not name:
            simpledialog.messagebox.showwarning("Warning", "Object name cannot be empty.")
            return False
        self.objects[name] = obj_data
        print(f"Added object: {name} - {obj_data}")
        if self.frames["ObjectCreationFrame"].winfo_exists():
            self.frames["ObjectCreationFrame"].update_objects_display()
        self._refresh_all_object_views()
        if self.frames["StepCreatorFrame"].winfo_exists():
            self.frames["StepCreatorFrame"].refresh_object_dropdowns()
        self.mark_sequence_modified()
        return True

    def _start_pixel_monitor_listener(self):
        # New pixel monitor popup with live coords & RGB; Enter to confirm
        if self.pixel_monitor_active:
            return
        self.pixel_monitor_active = True
        win = tk.Toplevel(self.root)
        self.pixel_capture_instruction_window = win
        win.title("Pixel Monitor")
        win.attributes('-topmost', True)
        win.lift(); win.focus_force();
        try:
            win.grab_set()
        except Exception:
            pass
        win.resizable(False, False)
        info = ttk.Label(win, text="Move mouse over pixel. Press Enter to confirm, Esc to cancel.")
        info.pack(padx=10, pady=(10, 4))
        lbl = ttk.Label(win, text="x=0, y=0 | RGB=(0,0,0)")
        lbl.pack(padx=10, pady=(0,4))
        color_canvas = tk.Canvas(win, width=40, height=40, highlightthickness=1, highlightbackground='black')
        color_canvas.pack(pady=(0,10))
        color_rect = color_canvas.create_rectangle(0, 0, 40, 40, fill="#000000", outline="#000000")

        stop_evt = threading.Event()
        latest = {'x': 0, 'y': 0, 'rgb': (0, 0, 0)}

        def approx_color_name(r, g, b):
            # Simple heuristic mapping
            h = max(r, g, b) - min(r, g, b)
            if r > 200 and g < 80 and b < 80:
                return 'red'
            if g > 200 and r < 80 and b < 80:
                return 'green'
            if b > 200 and r < 80 and g < 80:
                return 'blue'
            if r > 200 and g > 200 and b < 100:
                return 'yellow'
            if r > 180 and g > 150 and b < 80:
                return 'gold'
            if r > 120 and g < 80 and b < 80:
                return 'brown'
            if r > 200 and g > 200 and b > 200:
                return 'white'
            if r < 60 and g < 60 and b < 60:
                return 'black'
            return 'gray'

        def poll_mouse():
            try:
                while not stop_evt.is_set():
                    x, y = pyautogui.position()
                    try:
                        rgb = pyautogui.pixel(x, y)
                    except Exception:
                        rgb = (0, 0, 0)
                    latest['x'], latest['y'], latest['rgb'] = x, y, rgb
                    time.sleep(0.016)
            except Exception:
                if hasattr(self, 'logger'):
                    self.logger.exception('Pixel monitor poll error')

        def ui_update():
            if not win.winfo_exists():
                return
            x, y, (r, g, b) = latest['x'], latest['y'], latest['rgb']
            lbl.config(text=f"x={x}, y={y} | RGB=({r},{g},{b})")
            color_canvas.itemconfig(color_rect, fill=f"#{r:02x}{g:02x}{b:02x}", outline=f"#{r:02x}{g:02x}{b:02x}")
            win.after(16, ui_update)

        def confirm(_evt=None):
            try:
                x, y = latest['x'], latest['y']
                obj_name = simpledialog.askstring("Name Pixel Object", "Enter a name for this pixel:", parent=win)
                if obj_name:
                    obj_data = {"type": "pixel", "coords": (int(x), int(y)), "rgb": latest['rgb']}
                    if self.add_object(obj_name, obj_data):
                        simpledialog.messagebox.showinfo("Pixel Captured", f"Pixel '{obj_name}' at ({x},{y}) RGB={latest['rgb']}", parent=win)
            finally:
                stop()

        def stop(_evt=None):
            stop_evt.set()
            self.pixel_monitor_active = False
            if win and win.winfo_exists():
                win.destroy()

        win.bind('<Return>', confirm)
        win.bind('<Escape>', stop)
        threading.Thread(target=poll_mouse, daemon=True).start()
        ui_update()

    def _capture_pixel_under_mouse(self):
        if not self.pixel_monitor_active: return
        try:
            x, y = pyautogui.position()
            rgb = pyautogui.pixel(x, y)
            obj_name = simpledialog.askstring("Name Pixel Object", "Enter a name for this pixel object:", parent=self.root)
            if obj_name:
                obj_data = {"type": "pixel", "coords": (x, y), "rgb": rgb}
                if self.add_object(obj_name, obj_data):
                    simpledialog.messagebox.showinfo("Pixel Captured", f"Pixel '{obj_name}' captured at ({x},{y}) with RGB: {rgb}", parent=self.root)
        except Exception as e:
            simpledialog.messagebox.showerror("Error", f"Could not capture pixel: {e}", parent=self.root)
        finally:
            self.pixel_monitor_active = False
            if self.pixel_capture_instruction_window and self.pixel_capture_instruction_window.winfo_exists():
                self.pixel_capture_instruction_window.destroy()

    def create_region_grid_mode(self, creation_type=None):
        if creation_type is None:
            creation_type = self.frames["ObjectCreationFrame"].current_creation_type
        if self.grid_window and self.grid_window.winfo_exists(): self.grid_window.destroy()
        self.grid_window = tk.Toplevel(self.root)
        self.grid_window.attributes('-fullscreen', True); self.grid_window.attributes('-alpha', 0.4); self.grid_window.attributes('-topmost', True)
        self.grid_canvas = tk.Canvas(self.grid_window, bg='gray', highlightthickness=0); self.grid_canvas.pack(fill="both", expand=True)
        self.screen_width = self.root.winfo_screenwidth(); self.screen_height = self.root.winfo_screenheight()
        try:
            rows = self.grid_rows_var.get(); cols = self.grid_cols_var.get()
            if rows <= 0 or cols <= 0: raise ValueError("Grid dimensions must be positive.")
        except (tk.TclError, ValueError) as e:
            simpledialog.messagebox.showerror("Error", f"Invalid grid dimensions: {e}. Using 50px cell baseline.", parent=self.root)
            # fallback to baseline ~50px cells
            rows = max(1, self.screen_height // 50); cols = max(1, self.screen_width // 50)
            self.grid_rows_var.set(rows); self.grid_cols_var.set(cols)
        self.cell_width = self.screen_width / cols; self.cell_height = self.screen_height / rows
        self.selected_grid_cells = []; self._draw_grid_on_canvas()
        self.grid_canvas.bind("<Button-1>", self._on_grid_cell_click)
        # Scroll to change grid density: up => smaller boxes (more cells), down => bigger boxes
        self.grid_canvas.bind("<MouseWheel>", self._on_grid_scroll)
        # Linux X11 scroll events
        self.grid_canvas.bind("<Button-4>", lambda e: self._on_grid_scroll(delta=120))
        self.grid_canvas.bind("<Button-5>", lambda e: self._on_grid_scroll(delta=-120))
        self.grid_window.bind("<Escape>", lambda e: self._confirm_grid_selection(cancelled=True, creation_type=creation_type))
        confirm_bar = tk.Frame(self.grid_canvas, bg="lightgray", relief=tk.RAISED, borderwidth=1)
        self.grid_confirm_label = tk.Label(confirm_bar, text=f"{rows}x{cols} Grid. Scroll to change. ESC to cancel.", bg="lightgray")
        self.grid_confirm_label.pack(side=tk.LEFT, padx=10)
        tk.Button(confirm_bar, text="Confirm Selection", command=lambda: self._confirm_grid_selection(creation_type=creation_type)).pack(side=tk.LEFT, padx=10)
        self.grid_canvas.create_window(self.screen_width // 2, 30, window=confirm_bar, anchor="n")
        self.grid_window.focus_force()

    # --- Object overlay preview ---
    def preview_object_overlay(self, obj_name):
        try:
            obj = self.objects.get(obj_name)
            if not obj:
                self.show_toast(f"Object not found: {obj_name}")
                return
            ov = tk.Toplevel(self.root)
            ov.attributes('-fullscreen', True)
            ov.attributes('-alpha', 0.35)
            ov.attributes('-topmost', True)
            canvas = tk.Canvas(ov, bg='black', highlightthickness=0)
            canvas.pack(fill='both', expand=True)

            w, h = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            canvas.config(width=w, height=h)
            info_bar = tk.Frame(canvas, bg='lightgray')
            tk.Label(info_bar, text=f"Preview: {obj_name} (Esc to close)", bg='lightgray').pack(side=tk.LEFT, padx=8)
            tk.Button(info_bar, text='Open Grid', command=self.create_region_grid_mode).pack(side=tk.LEFT, padx=4)
            tk.Button(info_bar, text='Open Drag', command=self.create_region_drag_mode).pack(side=tk.LEFT, padx=4)
            canvas.create_window(w//2, 20, window=info_bar, anchor='n')

            def close(_e=None):
                if ov and ov.winfo_exists():
                    try:
                        self.root.unbind_all('<Escape>')
                    except Exception:
                        pass
                    ov.destroy()
            ov.bind('<Escape>', close)
            self.root.bind_all('<Escape>', close)

            t = obj.get('type')
            if t == 'image':
                coords = obj.get('capture_coords') or obj.get('coords')
                img_path = obj.get('image_path')
                if coords and img_path and os.path.exists(img_path):
                    try:
                        img = Image.open(img_path)
                        photo = ImageTk.PhotoImage(img)
                        x, y, w0, h0 = coords
                        canvas.create_image(x, y, image=photo, anchor='nw')
                        # keep reference
                        canvas._photo = photo
                        canvas.create_rectangle(x, y, x+w0, y+h0, outline='cyan', width=4)
                        # If image is tiny, also draw crosshair to help focus
                        if w0 <= 2 and h0 <= 2:
                            px, py = x + w0//2, y + h0//2
                            W, H = w, h
                            g = '#00FF5F'
                            canvas.create_line(0, py, px - 8, py, fill=g, width=3)
                            canvas.create_line(px + 8, py, W, py, fill=g, width=3)
                            canvas.create_line(px, 0, px, py - 8, fill=g, width=3)
                            canvas.create_line(px, py + 8, px, H, fill=g, width=3)
                            r = 8
                            canvas.create_oval(px - r, py - r, px + r, py + r, outline='red', fill='red', width=2)
                            canvas.create_oval(px - 2, py - 2, px + 2, py + 2, outline='blue', fill='blue', width=1)
                    except Exception as e:
                        self.logger.exception('Overlay image error')
                        self.show_toast('Failed to load image for overlay')
                else:
                    self.show_toast('Image object missing file or coords')
            elif t == 'region':
                coords = obj.get('coords')
                if coords:
                    x, y, w0, h0 = coords
                    width_px = 8
                    canvas.create_rectangle(x, y, x+w0, y+h0, outline='red', width=width_px)
                    # If this is a point-sized region, add crosshair to screen edges + large red dot with blue center
                    if w0 <= 2 and h0 <= 2:
                        cx, cy = x + w0//2, y + h0//2
                        W, H = w, h
                        g = '#00FF5F'
                        canvas.create_line(0, cy, cx - 8, cy, fill=g, width=3)
                        canvas.create_line(cx + 8, cy, W, cy, fill=g, width=3)
                        canvas.create_line(cx, 0, cx, cy - 8, fill=g, width=3)
                        canvas.create_line(cx, cy + 8, cx, H, fill=g, width=3)
                        r = 8
                        canvas.create_oval(cx - r, cy - r, cx + r, cy + r, outline='red', fill='red', width=2)
                        canvas.create_oval(cx - 2, cy - 2, cx + 2, cy + 2, outline='blue', fill='blue', width=1)
                else:
                    self.show_toast('Region object missing coords')
            elif t == 'pixel':
                coords = obj.get('coords')
                if coords and len(coords) >= 2:
                    px, py = coords[0], coords[1]
                    g = '#00FF5F'
                    # Crosshair to full screen edges
                    canvas.create_line(0, py, px - 8, py, fill=g, width=3)
                    canvas.create_line(px + 8, py, w, py, fill=g, width=3)
                    canvas.create_line(px, 0, px, py - 8, fill=g, width=3)
                    canvas.create_line(px, py + 8, px, h, fill=g, width=3)
                    r = 8
                    canvas.create_oval(px - r, py - r, px + r, py + r, outline='red', fill='red', width=2)
                    canvas.create_oval(px - 2, py - 2, px + 2, py + 2, outline='blue', fill='blue', width=1)
                else:
                    self.show_toast('Pixel object missing coords')
        except Exception as e:
            code = str(uuid.uuid4())[:8]
            if hasattr(self, 'logger'):
                self.logger.exception('Overlay error %s', code)
            self.show_toast(f'Overlay failure (code {code})')

    def _draw_grid_on_canvas(self):
        self.grid_canvas.delete("grid_line"); self.grid_canvas.delete("cell_highlight")
        rows = self.grid_rows_var.get(); cols = self.grid_cols_var.get()
        for r in range(rows):
            for c in range(cols):
                x1, y1 = c * self.cell_width, r * self.cell_height; x2, y2 = x1 + self.cell_width, y1 + self.cell_height
                if (r,c) in self.selected_grid_cells: self.grid_canvas.create_rectangle(x1, y1, x2, y2, fill="blue", outline="lightblue", stipple="gray50", tags="cell_highlight")
                if r < rows: self.grid_canvas.create_line(0, y2, self.screen_width, y2, fill="white", tags="grid_line", width=0.5)
                if c < cols: self.grid_canvas.create_line(x2, 0, x2, self.screen_height, fill="white", tags="grid_line", width=0.5)

    def _on_grid_scroll(self, event=None, delta=None):
        # Determine scroll direction
        d = delta if delta is not None else getattr(event, 'delta', 0)
        if d == 0:
            return
        inc = 3 if d > 0 else -3
        try:
            rows = max(1, self.grid_rows_var.get() + inc)
            cols = max(1, self.grid_cols_var.get() + inc)
            self.grid_rows_var.set(rows); self.grid_cols_var.set(cols)
            self.cell_width = self.screen_width / cols; self.cell_height = self.screen_height / rows
            # changing grid invalidates current cell selections
            self.selected_grid_cells = []
            self._draw_grid_on_canvas()
            if getattr(self, 'grid_confirm_label', None):
                self.grid_confirm_label.config(text=f"{rows}x{cols} Grid. Scroll to change. ESC to cancel.")
        except Exception:
            pass

    def _on_grid_cell_click(self, event):
        col = int(event.x // self.cell_width); row = int(event.y // self.cell_height); cell = (row, col)
        if cell in self.selected_grid_cells: self.selected_grid_cells.remove(cell)
        else: self.selected_grid_cells.append(cell)
        self._draw_grid_on_canvas()

    def _confirm_grid_selection(self, cancelled=False, creation_type=None):
        if cancelled or not self.selected_grid_cells:
            if self.grid_window and self.grid_window.winfo_exists(): self.grid_window.destroy()
            self.selected_grid_cells = []
            if not cancelled: simpledialog.messagebox.showinfo("Info", "No cells selected.", parent=self.root)
            return
        min_r,max_r = min(r for r,c in self.selected_grid_cells),max(r for r,c in self.selected_grid_cells)
        min_c,max_c = min(c for r,c in self.selected_grid_cells),max(c for r,c in self.selected_grid_cells)
        x1,y1 = min_c*self.cell_width, min_r*self.cell_height
        width,height = (max_c-min_c+1)*self.cell_width, (max_r-min_r+1)*self.cell_height
        coords = (int(x1),int(y1),int(width),int(height))
        if creation_type is None:
            creation_type = self.frames["ObjectCreationFrame"].current_creation_type
        obj_name = simpledialog.askstring(f"Name {creation_type.capitalize()} Object", f"Enter name for selected {creation_type}:", parent=self.root)
        if obj_name:
            if creation_type == "region":
                obj_data={"type":"region","mode":"grid","coords":coords,"cells":list(self.selected_grid_cells)}
                if self.add_object(obj_name, obj_data): simpledialog.messagebox.showinfo("Region Created", f"Region '{obj_name}' created.", parent=self.root)
            elif creation_type == "image":
                try:
                    self.root.withdraw(); time.sleep(0.2); img = pyautogui.screenshot(region=coords); self.root.deiconify()
                    base_img_filename = f"{obj_name.replace(' ', '_').replace('.', '_')}.png"; final_abs_img_path = ""
                    if self.current_project_path:
                        images_dir = os.path.join(self.current_project_path, "images"); os.makedirs(images_dir, exist_ok=True)
                        final_abs_img_path = os.path.join(images_dir, base_img_filename)
                    else:
                        final_abs_img_path = os.path.join(os.getcwd(), base_img_filename)
                        simpledialog.messagebox.showinfo("Image Saved (No Project)",f"Image: {final_abs_img_path}\nRelative after 'Save As...'.",parent=self.root)
                    img.save(final_abs_img_path)
                    obj_data={"type":"image","mode":"grid","image_path":final_abs_img_path,"capture_coords":coords,"confidence":0.8}
                    if self.add_object(obj_name,obj_data): simpledialog.messagebox.showinfo("Image Created",f"Image '{obj_name}' captured.",parent=self.root)
                except Exception as e: self.root.deiconify(); simpledialog.messagebox.showerror("Error",f"Capture image error: {e}",parent=self.root)
        if self.grid_window and self.grid_window.winfo_exists(): self.grid_window.destroy(); self.selected_grid_cells = []

    def create_region_drag_mode(self, creation_type=None):
        if creation_type is None:
            creation_type = self.frames["ObjectCreationFrame"].current_creation_type
        if self.drag_select_window and self.drag_select_window.winfo_exists(): return
        self.drag_select_window = tk.Toplevel(self.root)
        self.drag_select_window.attributes('-fullscreen',True); self.drag_select_window.attributes('-alpha',0.3); self.drag_select_window.attributes('-topmost',True)
        drag_canvas = tk.Canvas(self.drag_select_window,bg="gray",cursor="crosshair",highlightthickness=0); drag_canvas.pack(fill="both",expand=True)
        tk.Label(drag_canvas,text="Click & drag. Release to confirm. ESC to cancel.",bg="lightyellow",fg="black").place(x=10,y=10)
        def on_b1_press(event): self.drag_start_x=event.x; self.drag_start_y=event.y; self.drag_rect_id=drag_canvas.create_rectangle(self.drag_start_x,self.drag_start_y,self.drag_start_x,self.drag_start_y,outline='red',width=2)
        def on_b1_motion(event):
            if self.drag_rect_id: drag_canvas.coords(self.drag_rect_id,self.drag_start_x,self.drag_start_y,event.x,event.y)
        def on_b1_release(event):
            if self.drag_start_x is None: return
            x1,y1=min(self.drag_start_x,event.x),min(self.drag_start_y,event.y); x2,y2=max(self.drag_start_x,event.x),max(self.drag_start_y,event.y)
            self.drag_select_window.destroy(); self.drag_select_window=None; self.drag_start_x,self.drag_start_y,self.drag_rect_id = None,None,None
            if abs(x1-x2)<5 or abs(y1-y2)<5: simpledialog.messagebox.showinfo("Info","Selection too small.",parent=self.root); return
            coords=(int(x1),int(y1),int(x2-x1),int(y2-y1))
            obj_name = simpledialog.askstring(f"Name {creation_type.capitalize()} Object",f"Enter name:",parent=self.root)
            if obj_name:
                if creation_type == "region":
                    obj_data={"type":"region","mode":"drag","coords":coords}
                    if self.add_object(obj_name,obj_data): simpledialog.messagebox.showinfo("Region Created",f"Region '{obj_name}' created.",parent=self.root)
                elif creation_type == "image":
                    try:
                        self.root.withdraw(); time.sleep(0.2); img = pyautogui.screenshot(region=coords); self.root.deiconify()
                        base_img_filename=f"{obj_name.replace(' ','_').replace('.','_')}.png"; final_abs_img_path=""
                        if self.current_project_path:
                            images_dir=os.path.join(self.current_project_path,"images"); os.makedirs(images_dir,exist_ok=True)
                            final_abs_img_path=os.path.join(images_dir,base_img_filename)
                        else:
                            final_abs_img_path=os.path.join(os.getcwd(),base_img_filename)
                            simpledialog.messagebox.showinfo("Image Saved (No Project)",f"Image: {final_abs_img_path}\nRelative after 'Save As...'.",parent=self.root)
                        img.save(final_abs_img_path)
                        obj_data={"type":"image","mode":"drag","image_path":final_abs_img_path,"capture_coords":coords,"confidence":0.8}
                        if self.add_object(obj_name,obj_data): simpledialog.messagebox.showinfo("Image Created",f"Image '{obj_name}' captured.",parent=self.root)
                    except Exception as e: self.root.deiconify(); simpledialog.messagebox.showerror("Error",f"Capture image error: {e}",parent=self.root)
        def on_escape_drag(event=None):
            if self.drag_select_window: self.drag_select_window.destroy(); self.drag_select_window=None
            self.drag_start_x,self.drag_start_y,self.drag_rect_id=None,None,None; print("Drag selection cancelled.")
        drag_canvas.bind("<ButtonPress-1>",on_b1_press); drag_canvas.bind("<B1-Motion>",on_b1_motion)
        drag_canvas.bind("<ButtonRelease-1>",on_b1_release); self.drag_select_window.bind("<Escape>",on_escape_drag)
        self.drag_select_window.focus_force()

    def _check_unsaved_changes(self):
        if self.sequence_modified:
            response = simpledialog.messagebox.askyesnocancel("Unsaved Changes", f"Sequence '{self.current_sequence_name}' has unsaved changes. Save now?", parent=self.root)
            if response is True: return self.save_sequence()
            elif response is False: return True
            else: return False
        return True

    def _on_close(self):
        if self._check_unsaved_changes():
            self.root.destroy()

    def new_sequence(self):
        if not self._check_unsaved_changes(): return
        self.objects={}; self.current_steps=[]
        self.frames["StepCreatorFrame"].clear_and_rebuild_steps([])
        self.loop_count.set(1); self.current_project_path=None; self.current_sequence_name=DEFAULT_PROJECT_NAME
        self.mark_sequence_modified(False)
        self.frames["ObjectCreationFrame"].update_objects_display(); self.frames["MainFrame"].refresh_content()
        print("New sequence created.")

    def save_sequence(self):
        if not self.current_project_path: return self.save_sequence_as()
        else:
            self.frames["StepCreatorFrame"].finalize_steps_for_controller()
            project_dir=self.current_project_path; sequence_filename=os.path.join(project_dir,f"{self.current_sequence_name}.json")
            project_images_dir=os.path.join(project_dir,"images"); os.makedirs(project_images_dir,exist_ok=True)
            data_to_save={"sequence_name":self.current_sequence_name,"loop_count":self.loop_count.get(),"objects":{},"steps":self.current_steps}
            for obj_name,obj_data_in_memory in self.objects.items():
                obj_data_for_json=obj_data_in_memory.copy()
                if obj_data_for_json.get("type")=="image":
                    current_abs_image_path=obj_data_in_memory.get("image_path")
                    if not current_abs_image_path or not os.path.isabs(current_abs_image_path):
                        print(f"Warning: Img obj '{obj_name}' invalid path: {current_abs_image_path}. Skipping."); data_to_save["objects"][obj_name]=obj_data_for_json; continue
                    if not os.path.exists(current_abs_image_path):
                        print(f"Warning: Img file for '{obj_name}' not found: {current_abs_image_path}. Storing as is."); data_to_save["objects"][obj_name]=obj_data_for_json; continue
                    img_basename=os.path.basename(current_abs_image_path)
                    target_abs_path_in_project_images=os.path.join(project_images_dir,img_basename)
                    norm_current_path=os.path.normpath(current_abs_image_path); norm_target_path=os.path.normpath(target_abs_path_in_project_images)
                    if norm_current_path != norm_target_path:
                        try:
                            shutil.copy2(current_abs_image_path,target_abs_path_in_project_images); print(f"Copied img for '{obj_name}' to: {target_abs_path_in_project_images}")
                            self.objects[obj_name]["image_path"]=target_abs_path_in_project_images
                        except Exception as e: print(f"Error copying img {current_abs_image_path}: {e}"); simpledialog.messagebox.showerror("Save Error",f"Could not copy img asset {img_basename} for {obj_name}",parent=self.root)
                    obj_data_for_json["image_path"]=os.path.join("images",img_basename)
                data_to_save["objects"][obj_name]=obj_data_for_json
            try:
                with open(sequence_filename,'w') as f: json.dump(data_to_save,f,indent=4)
                simpledialog.messagebox.showinfo("Save Sequence",f"Sequence '{self.current_sequence_name}' saved.",parent=self.root)
                self.mark_sequence_modified(False); self.frames["MainFrame"].refresh_content(); return True
            except Exception as e: simpledialog.messagebox.showerror("Save Error",f"Could not save seq: {e}",parent=self.root); return False

    def save_sequence_as(self):
        self.frames["StepCreatorFrame"].finalize_steps_for_controller()
        project_dir = filedialog.askdirectory(title="Select Project Folder for Sequence", parent=self.root)
        if not project_dir: return False
        default_name=self.current_sequence_name if self.current_sequence_name!=DEFAULT_PROJECT_NAME else "MyNewSequence"
        seq_name=simpledialog.askstring("Sequence Name","Enter name for sequence:",initialvalue=default_name,parent=self.root)
        if not seq_name: return False
        self.current_project_path=os.path.join(project_dir,seq_name); self.current_sequence_name=seq_name
        return self.save_sequence()

    def load_sequence(self):
        if not self._check_unsaved_changes(): return
        filepath = filedialog.askopenfilename(title="Load Sequence File",defaultextension=".json",filetypes=[("JSON files","*.json"),("All files","*.*")],parent=self.root)
        if not filepath: return
        try:
            with open(filepath,'r') as f: loaded_data=json.load(f)
            self.current_project_path=os.path.dirname(filepath)
            self.current_sequence_name=loaded_data.get("sequence_name",os.path.splitext(os.path.basename(filepath))[0])
            temp_objects={};
            for obj_name,obj_data in loaded_data.get("objects",{}).items():
                obj_copy=obj_data.copy()
                if obj_copy.get("type")=="image" and obj_copy.get("image_path"):
                    relative_img_path=obj_copy["image_path"]
                    abs_image_path=os.path.join(self.current_project_path,relative_img_path)
                    if os.path.exists(abs_image_path): obj_copy["image_path"]=abs_image_path
                    else: print(f"Warning: Img asset not found for '{obj_name}': {abs_image_path}")
                temp_objects[obj_name]=obj_copy
            self.objects=temp_objects
            self.current_steps=loaded_data.get("steps",[]); self.loop_count.set(loaded_data.get("loop_count",1))
            self.frames["ObjectCreationFrame"].update_objects_display()
            self.frames["StepCreatorFrame"].clear_and_rebuild_steps(self.current_steps)
            self.frames["MainFrame"].refresh_content(); self.mark_sequence_modified(False)
            simpledialog.messagebox.showinfo("Load Sequence",f"Sequence '{self.current_sequence_name}' loaded.",parent=self.root)
        except Exception as e:
            simpledialog.messagebox.showerror("Load Error",f"Could not load sequence: {e}",parent=self.root)
            self.new_sequence()

    def run_sequence(self):
        self.frames["StepCreatorFrame"].finalize_steps_for_controller()
        if not self.current_steps:
            simpledialog.messagebox.showinfo("Run Sequence", "No steps to run.", parent=self.root); return
        try:
            loops_to_run = self.loop_count.get()
            if loops_to_run < 0: simpledialog.messagebox.showerror("Error","Loop count cannot be negative.",parent=self.root); return
        except tk.TclError: simpledialog.messagebox.showerror("Error","Invalid loop count.",parent=self.root); return

        self.root.iconify(); time.sleep(0.5)
        pyautogui.FAILSAFE = True

        print(f"--- Running Sequence: {self.current_sequence_name} ---")
        is_infinite_loop = (loops_to_run == 0)
        if is_infinite_loop: print("Looping indefinitely. Ctrl+C or Failsafe to stop.")
        else: print(f"Looping {loops_to_run} times.")

        current_loop_iter = 0
        try:
            while True: # Outer loop for sequence repetitions
                current_loop_iter += 1
                if not is_infinite_loop and current_loop_iter > loops_to_run:
                    break # All specified loops are done

                if is_infinite_loop:
                    print(f"Executing Loop {current_loop_iter}")
                else:
                    print(f"Executing Loop {current_loop_iter}/{loops_to_run}")

                program_counter = 0
                while program_counter < len(self.current_steps): # Inner loop for steps
                    step = self.current_steps[program_counter]
                    print(f"  Step {program_counter + 1}/{len(self.current_steps)}: Action: {step['action']}, Object: {step.get('object_name', 'N/A')}, Params: {step.get('params', {})}")

                    obj_name = step.get("object_name"); action = step.get("action"); params = step.get("params", {})
                    target_object = self.objects.get(obj_name) if obj_name else None
                    
                    jump_to_pc = -1 # Use -1 to indicate no jump, otherwise set to target 0-based PC

                    try:
                        image_path_to_use = None
                        if target_object and target_object.get("type") == "image":
                            image_path_to_use = target_object.get("image_path")
                            if image_path_to_use and not os.path.exists(image_path_to_use):
                                print(f"    ERROR: Image file missing for object '{obj_name}' at path: {image_path_to_use}")

                        # --- LOGIC ACTIONS ---
                        if action == "Goto Step":
                            target_step_num = params.get("target_step")
                            if isinstance(target_step_num, int) and 1 <= target_step_num <= len(self.current_steps):
                                jump_to_pc = target_step_num - 1 
                            else: print(f"    WARN: Invalid target step for Goto: {target_step_num}.")
                        
                        elif action == "If Image Found":
                            condition_obj_name = params.get("condition_object_name")
                            condition_object = self.objects.get(condition_obj_name)
                            then_step = params.get("then_step"); else_step = params.get("else_step")
                            if condition_object and condition_object.get("type") == "image":
                                cond_img_path = condition_object.get("image_path")
                                confidence = params.get("confidence", condition_object.get("confidence", 0.8))
                                if cond_img_path and os.path.exists(cond_img_path) and pyautogui.locateOnScreen(cond_img_path, confidence=confidence):
                                    print(f"    IF: Image '{condition_obj_name}' FOUND.")
                                    if isinstance(then_step, int) and 1 <= then_step <= len(self.current_steps):
                                        jump_to_pc = then_step - 1
                                    elif then_step is not None: print(f"    WARN: Invalid 'Then' step for If Image Found: {then_step}.")
                                else: # Image NOT found
                                    print(f"    IF: Image '{condition_obj_name}' NOT found.")
                                    if isinstance(else_step, int) and 1 <= else_step <= len(self.current_steps):
                                        jump_to_pc = else_step - 1
                                    elif else_step is not None: print(f"    WARN: Invalid 'Else' step for If Image Found: {else_step}.")
                            else: print(f"    WARN: Invalid condition object for 'If Image Found': {condition_obj_name}.")

                        elif action == "If Pixel Color":
                            condition_obj_name = params.get("condition_object_name")
                            condition_object = self.objects.get(condition_obj_name)
                            expected_rgb_param = params.get("expected_rgb")
                            expected_rgb = tuple(expected_rgb_param) if isinstance(expected_rgb_param, list) else (expected_rgb_param if isinstance(expected_rgb_param, tuple) else (condition_object.get("rgb") if condition_object else None))
                            then_step = params.get("then_step"); else_step = params.get("else_step")
                            if condition_object and condition_object.get("type") == "pixel" and expected_rgb:
                                px, py = condition_object["coords"]
                                current_rgb = pyautogui.pixel(px,py)
                                if current_rgb == expected_rgb:
                                    print(f"    IF: Pixel '{condition_obj_name}' color MATCHED.")
                                    if isinstance(then_step, int) and 1 <= then_step <= len(self.current_steps):
                                        jump_to_pc = then_step - 1
                                    elif then_step is not None: print(f"    WARN: Invalid 'Then' step for If Pixel Color: {then_step}.")
                                else: # Pixel color NOT matched
                                    print(f"    IF: Pixel '{condition_obj_name}' color ({current_rgb}) did NOT match {expected_rgb}.")
                                    if isinstance(else_step, int) and 1 <= else_step <= len(self.current_steps):
                                        jump_to_pc = else_step - 1
                                    elif else_step is not None: print(f"    WARN: Invalid 'Else' step for If Pixel Color: {else_step}.")
                            else: print(f"    WARN: Invalid condition object/RGB for 'If Pixel Color'. Expected RGB was {expected_rgb}")
                        
                        # --- STANDARD ACTIONS (Only if no logic jump will occur from this step) ---
                        if jump_to_pc == -1 : # No jump determined by a logic action yet
                            if target_object: # Object-based actions
                                obj_type = target_object.get("type"); obj_coords = target_object.get("coords")
                                if action == "Click":
                                    button_type = params.get("button", "left"); num_clicks = params.get("clicks", 1)
                                    interval_s = params.get("interval", 0.1 if num_clicks > 1 else 0.0)
                                    click_x, click_y = None, None
                                    if obj_type == "region" and obj_coords: click_x, click_y = obj_coords[0]+obj_coords[2]/2, obj_coords[1]+obj_coords[3]/2
                                    elif obj_type == "pixel" and obj_coords: click_x, click_y = obj_coords[0], obj_coords[1]
                                    elif obj_type == "image" and image_path_to_use:
                                        loc = pyautogui.locateCenterOnScreen(image_path_to_use, confidence=params.get("confidence", target_object.get("confidence",0.8)))
                                        if loc: click_x, click_y = loc
                                        else: print(f"    WARN: Image '{obj_name}' not found for click.") 
                                    else: print(f"    WARN: Cannot Click obj '{obj_name}' type '{obj_type}'.")
                                    if click_x is not None: pyautogui.click(x=click_x,y=click_y,clicks=num_clicks,interval=interval_s,button=button_type); print(f"    Clicked {button_type} {num_clicks}x at ({click_x:.0f},{click_y:.0f})")
                                    else: print(f"    WARN: Click coords not determined for {obj_name}.")
                                elif action == "Wait for Image" and obj_type == "image" and image_path_to_use:
                                    start_time = time.time(); timeout = params.get("timeout_s", 10); found = False
                                    while time.time() - start_time < timeout:
                                        if pyautogui.locateOnScreen(image_path_to_use, confidence=params.get("confidence", target_object.get("confidence",0.8))):
                                            print(f"    Image '{obj_name}' found."); found = True; break
                                        time.sleep(0.25) 
                                    if not found: print(f"    TIMEOUT: Image '{obj_name}' not found after {timeout}s.")
                                elif action == "Wait for Pixel Color" and obj_type == "pixel":
                                    expected_rgb_wfp = params.get("expected_rgb")
                                    expected_rgb_wfp = tuple(expected_rgb_wfp) if isinstance(expected_rgb_wfp, list) else (expected_rgb_wfp if isinstance(expected_rgb_wfp, tuple) else target_object.get("rgb"))
                                    if not expected_rgb_wfp: print(f"    ERROR: No RGB for pixel '{obj_name}'.")
                                    else:
                                        timeout = params.get("timeout_s",10); start_time=time.time(); found_color=False
                                        while time.time()-start_time < timeout:
                                            current_rgb = pyautogui.pixel(obj_coords[0],obj_coords[1])
                                            if current_rgb == expected_rgb_wfp: print(f"    Pixel color matched."); found_color=True; break
                                            time.sleep(0.25)
                                        if not found_color: print(f"    TIMEOUT: Pixel color not matched. Last: {current_rgb}")
                            # Global actions
                            if action == "Wait":
                                duration = params.get("duration_s", 1.0); min_dur = params.get("min_s"); max_dur = params.get("max_s")
                                if min_dur is not None and max_dur is not None: wait_time=random.uniform(min_dur,max_dur); print(f"    Random Wait: {wait_time:.2f}s"); time.sleep(wait_time)
                                else: print(f"    Static Wait: {duration}s"); time.sleep(duration)
                            elif action == "Keyboard Input": 
                                text_to_type = params.get("text_to_type", "")
                                if text_to_type: pyautogui.typewrite(text_to_type, interval=params.get("interval", 0.01)); print(f"    Typed: '{text_to_type}'")
                                else: print(f"    WARN: No text specified for Keyboard Input.")
                            elif action == "Press Key": 
                                key_to_press = params.get("key_to_press")
                                if key_to_press: pyautogui.press(key_to_press); print(f"    Pressed Key: '{key_to_press}'")
                                else: print(f"    WARN: No key specified for Press Key.")
                            elif action == "Hotkey Combo": 
                                selected_hotkey_name = params.get("selected_hotkey_name")
                                if selected_hotkey_name and selected_hotkey_name in PREDEFINED_HOTKEYS:
                                    keys_to_press = PREDEFINED_HOTKEYS[selected_hotkey_name]
                                    pyautogui.hotkey(*keys_to_press); print(f"    Executed Hotkey Combo: {selected_hotkey_name} ({keys_to_press})")
                                else: print(f"    WARN: Invalid or no hotkey selected: '{selected_hotkey_name}'")
                            elif action == "Scroll": 
                                direction=params.get("direction","down"); amount=params.get("amount",10)
                                scroll_x=params.get("x"); scroll_y=params.get("y")
                                scroll_val = -amount if direction in ["down","left"] else amount
                                if direction in ["up","down"]: pyautogui.scroll(scroll_val,x=scroll_x,y=scroll_y)
                                elif direction in ["left","right"]: pyautogui.hscroll(scroll_val,x=scroll_x,y=scroll_y)
                                print(f"    Scrolled {direction} by {abs(amount)}" + (f" at ({scroll_x},{scroll_y})" if scroll_x is not None else ""))
                    
                    except pyautogui.FailSafeException: print("!!! FAILSAFE TRIGGERED !!!"); self.root.deiconify(); return
                    except Exception as e:
                        import traceback
                        print(f"    ERROR executing step {program_counter + 1} ({action} on {obj_name}): {e}")
                        traceback.print_exc()

                    if jump_to_pc != -1:
                        program_counter = jump_to_pc
                    else:
                        program_counter += 1
                # End of inner while (steps loop)
            # End of outer while (sequence repetitions loop)
        except KeyboardInterrupt: print("\n--- Execution Interrupted by User (Ctrl+C) ---")
        finally:
            self.root.deiconify()
            print(f"--- Sequence Finished: {self.current_sequence_name} ---")


# --- UI Frame Classes ---
class BaseFrame(tk.Frame):
    def __init__(self, parent, controller):
        super().__init__(parent)
        self.controller = controller
        # Use a neutral background that doesn't fight the system theme
        try:
            self.configure(bg=self.master.cget("bg"))
        except Exception:
            self.configure(bg="#F5F6F8")

class MainFrame(BaseFrame):
    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        ttk.Label(self, text="Automation Tool", font=("Arial", 16, "bold")).pack(pady=10)
        btn_frame_new = ttk.Frame(self); btn_frame_new.pack(pady=5, fill="x", padx=20)
        ttk.Button(btn_frame_new, text="New Sequence", command=controller.new_sequence).pack(pady=3, fill="x")
        ttk.Button(btn_frame_new, text="Instructions", command=lambda: controller.show_frame("InstructionsFrame")).pack(pady=3, fill="x")

        ttk.Label(btn_frame_new, text="Create & Edit", font=("Arial", 12, "underline")).pack(pady=(8,0))

        btn_obj = ttk.Button(btn_frame_new, text="Object Creation", command=controller.open_object_creation_window)
        btn_obj.pack(pady=3, fill="x")
        def _obj_same_window(_e=None):
            controller.show_frame("ObjectCreationFrame"); return "break"
        btn_obj.bind("<Shift-Button-1>", _obj_same_window)
        btn_step = ttk.Button(btn_frame_new, text="Step Creator", command=controller.open_step_creator_window)
        btn_step.pack(pady=3, fill="x")
        def _step_same_window(_e=None):
            controller.show_frame("StepCreatorFrame"); return "break"
        btn_step.bind("<Shift-Button-1>", _step_same_window)


        ttk.Separator(self, orient="horizontal").pack(fill="x", pady=10, padx=20)
        ttk.Label(self, text="File Operations", font=("Arial", 12, "underline")).pack(pady=(8,0))
        file_ops_frame = ttk.Frame(self); file_ops_frame.pack(pady=5,padx=20,fill="x")
        ttk.Button(file_ops_frame, text="Load Sequence", command=controller.load_sequence).pack(side=tk.LEFT, expand=True, fill="x", padx=(0,3))
        ttk.Button(file_ops_frame, text="Save Sequence As...", command=controller.save_sequence_as).pack(side=tk.LEFT, expand=True, fill="x", padx=(3,0))
        loaded_seq_frame = ttk.Frame(self); loaded_seq_frame.pack(pady=5,padx=20,fill="x")
        ttk.Label(loaded_seq_frame,text="Current:").pack(side=tk.LEFT)
        self.loaded_seq_label = ttk.Label(loaded_seq_frame,text="No sequence loaded", anchor="w", relief=tk.SUNKEN)
        self.loaded_seq_label.pack(side=tk.LEFT,expand=True,fill="x")

        loop_frame = ttk.Frame(self); loop_frame.pack(pady=8,padx=20,fill="x")
        ttk.Label(loop_frame,text="Loops (0=inf):").pack(side=tk.LEFT)
        ttk.Entry(loop_frame,textvariable=controller.loop_count,width=6,justify="center").pack(side=tk.LEFT,padx=5)

        ttk.Button(self,text="Run Sequence",width=24,command=controller.run_sequence).pack(pady=15,padx=20,fill="x")

    def refresh_content(self):
        if self.controller.current_sequence_name == DEFAULT_PROJECT_NAME and not self.controller.current_project_path:
            self.loaded_seq_label.config(text="No sequence loaded")
        else:
            self.loaded_seq_label.config(text=self.controller.current_sequence_name)


class ObjectCreationFrame(BaseFrame):
    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        self.current_creation_type = "region"
        ttk.Label(self, text="Object Creation", font=("Arial", 16, "bold")).pack(pady=10)
        region_frame = ttk.Labelframe(self, text="Region Creation", padding=10); region_frame.pack(pady=5,padx=10,fill="x")
        grid_dim_frame = ttk.Frame(region_frame); grid_dim_frame.pack(fill="x")
        ttk.Label(grid_dim_frame, text="Grid (W x H):").pack(side=tk.LEFT,padx=(0,2))
        ttk.Entry(grid_dim_frame, textvariable=controller.grid_cols_var, width=4).pack(side=tk.LEFT)
        ttk.Label(grid_dim_frame, text="x").pack(side=tk.LEFT,padx=1)
        ttk.Entry(grid_dim_frame, textvariable=controller.grid_rows_var, width=4).pack(side=tk.LEFT,padx=(0,5))
        ttk.Button(grid_dim_frame, text="Grid Mode", command=lambda:self.set_creation_type_and_run("region",controller.create_region_grid_mode)).pack(side=tk.LEFT,expand=True,fill="x")
        ttk.Button(region_frame, text="Drag Mode", command=lambda:self.set_creation_type_and_run("region",controller.create_region_drag_mode)).pack(pady=3,fill="x")
        ttk.Button(region_frame, text="Point (Mouse Pos)", command=lambda: self.create_point_region_from_mouse()).pack(pady=3,fill="x")
        ttk.Button(region_frame, text="Pixel Monitor", command=controller._start_pixel_monitor_listener).pack(pady=3,fill="x")
        image_frame = ttk.Labelframe(self, text="Image Creation", padding=10); image_frame.pack(pady=5,padx=10,fill="x")
        ttk.Button(image_frame, text="Grid Mode (Capture)", command=lambda:self.set_creation_type_and_run("image",controller.create_region_grid_mode)).pack(pady=3,fill="x")
        ttk.Button(image_frame, text="Drag Mode (Capture)", command=lambda:self.set_creation_type_and_run("image",controller.create_region_drag_mode)).pack(pady=3,fill="x")
        sound_frame = ttk.Labelframe(self, text="Sound Creation (Future)", padding=10); sound_frame.pack(pady=5,padx=10,fill="x")
        ttk.Button(sound_frame, text="Sound Recording", state=tk.DISABLED).pack(pady=3,fill="x")
        self.objects_list_frame=ttk.Labelframe(self, text="Created Objects", padding=10); self.objects_list_frame.pack(pady=5,padx=10,fill="both",expand=True)
        cols = ("Name", "Type", "Details")
        self.objects_tree = ttk.Treeview(self.objects_list_frame, columns=cols, show='headings', height=8)
        for c in cols:
            self.objects_tree.heading(c, text=c)
        self.objects_tree.column("Name", width=200)
        self.objects_tree.column("Type", width=80)
        self.objects_tree.column("Details", width=420)
        self.objects_tree.pack(fill="both", expand=True)
        self.objects_tree.bind('<Double-1>', self._on_object_double_click)
        btn_bar = ttk.Frame(self.objects_list_frame)
        btn_bar.pack(fill='x', pady=4)
        ttk.Button(btn_bar, text='Delete Selected', command=self._delete_selected_object).pack(side=tk.RIGHT)
        ttk.Button(self, text="Back to Main Menu", command=lambda: controller.show_frame("MainFrame")).pack(pady=10, side=tk.BOTTOM)
    def set_creation_type_and_run(self, c_type, func_to_run):
        self.current_creation_type = c_type
        try:
            func_to_run(c_type)
        except TypeError:
            func_to_run()
    def create_point_region_from_mouse(self):
        # Popup with live coords; Enter to confirm, Esc to cancel
        pop = tk.Toplevel(self.controller.root)
        pop.title("Select Mouse Point")
        pop.attributes('-topmost', True)
        pop.lift(); pop.focus_force();
        try:
            pop.grab_set()
        except Exception:
            pass
        ttk.Label(pop, text="Move mouse to target, press Enter to confirm, Esc to cancel.").pack(padx=10, pady=(10,4))
        lab = ttk.Label(pop, text="x=0, y=0")
        lab.pack(padx=10, pady=(0,10))
        stop_evt = threading.Event()
        latest = {'x': 0, 'y': 0}

        def poll():
            while not stop_evt.is_set():
                x, y = pyautogui.position()
                latest['x'], latest['y'] = x, y
                time.sleep(0.016)

        def ui_update():
            if not pop.winfo_exists():
                return
            lab.config(text=f"x={latest['x']}, y={latest['y']}")
            pop.after(16, ui_update)

        def confirm(_e=None):
            try:
                x, y = latest['x'], latest['y']
                obj_name = simpledialog.askstring("Name Region Point", "Enter name:", parent=pop)
                if obj_name:
                    coords = (int(x), int(y), 1, 1)
                    obj_data = {"type": "region", "mode": "point", "coords": coords}
                    if self.controller.add_object(obj_name, obj_data):
                        self.controller.show_toast(f"Point '{obj_name}' at ({x},{y}) saved")
            finally:
                cancel()

        def cancel(_e=None):
            stop_evt.set()
            if pop and pop.winfo_exists(): pop.destroy()

        threading.Thread(target=poll, daemon=True).start()
        ui_update()
        pop.bind('<Return>', confirm)
        pop.bind('<Escape>', cancel)
    def update_objects_display(self):
        try:
            for i in self.objects_tree.get_children(''):
                self.objects_tree.delete(i)
            for name,data in self.controller.objects.items():
                obj_type=data.get("type","N/A"); details=""
                display_type = obj_type
                if obj_type in ("region","image") and data.get('coords'):
                    details=f"Coords: {data.get('coords')}"
                if obj_type=="image" and data.get('image_path'):
                    details+=f", Path: {os.path.basename(data['image_path'])}"
                elif obj_type=="pixel":
                    details=f"Coords: {data.get('coords')}, RGB: {data.get('rgb')}"
                    display_type = "point"
                if data.get('mode') == 'point' and obj_type == 'region':
                    display_type = "point"
                self.objects_tree.insert('', 'end', values=(name, display_type, details))
        except Exception as e:
            if hasattr(self.controller,'logger'):
                self.controller.logger.exception('update_objects_display failed')
    def refresh_content(self): self.update_objects_display()

    def _delete_selected_object(self):
        try:
            sel = self.objects_tree.selection()
            if not sel:
                return
            vals = self.objects_tree.item(sel[0], 'values')
            if not vals:
                return
            name = vals[0]
            if simpledialog.messagebox.askyesno('Delete Object', f"Delete object '{name}'? This cannot be undone.", parent=self.controller.root):
                if name in self.controller.objects:
                    del self.controller.objects[name]
                    self.update_objects_display()
                    try:
                        self.controller.frames["StepCreatorFrame"].refresh_object_dropdowns()
                    except Exception:
                        pass
                    self.controller.show_toast(f"Deleted object: {name}")
                    self.controller.mark_sequence_modified()
        except Exception as e:
            if hasattr(self.controller, 'logger'):
                self.controller.logger.exception('Delete object failed')
    def _on_object_double_click(self, event=None):
        try:
            sel = self.objects_tree.selection()
            if not sel: return
            item = sel[0]
            vals = self.objects_tree.item(item, 'values')
            if not vals: return
            name = vals[0]
            self.controller.preview_object_overlay(name)
        except Exception as e:
            if hasattr(self.controller,'logger'):
                self.controller.logger.exception('object overlay failed')


class StepCreatorFrame(BaseFrame):
    def _type_abbrev(self, obj):
        if not obj:
            return "-"
        t = obj.get("type")
        if t == "image":
            return "img"
        if t == "pixel" or obj.get("mode") == "point":
            return "point"
        if t == "region":
            return "reg"
        return "-"

    def _display_name_for_object(self, name):
        if not name:
            return "(Global/Control)"
        obj = self.controller.objects.get(name)
        if not obj:
            return name
        ab = self._type_abbrev(obj)
        return f"{name} [ {ab} ]"

    def _get_object_display_names(self):
        names = [self._display_name_for_object(n) for n in self.controller.get_object_names()]
        names.append("(Global/Control)")
        return names

    def _name_from_display(self, display):
        if display == "(Global/Control)":
            return None
        if display.endswith(" ]") and " [ " in display:
            return display.rsplit(" [ ", 1)[0]
        return display
    ACTION_CONFIG = {
        "region": ["Click", "Type into Region (Future)"],
        "pixel": ["Click", "Wait for Pixel Color"],
        "image": ["Click", "Wait for Image"],
        "_global_": ["Wait", "Keyboard Input", "Press Key", "Hotkey Combo", "Scroll"],
        "_control_": ["If Image Found", "If Pixel Color", "Goto Step"]
    }

    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        self.step_widgets = []

        ttk.Label(self, text="Step Creator", font=("Segoe UI", 14, "bold")).pack(pady=(6,2))

        toolbar_frame = ttk.Frame(self)
        toolbar_frame.pack(fill="x", padx=12, pady=(0,6))
        ttk.Button(toolbar_frame, text="+ Add Step", command=self.add_step_row).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar_frame, text="Save Sequence", command=self.controller.save_sequence).pack(side=tk.LEFT, padx=4)
        ttk.Button(toolbar_frame, text="Back to Main Menu", command=self._back_to_main).pack(side=tk.RIGHT)

        header_frame = ttk.Frame(self)
        header_frame.pack(fill="x", padx=12, pady=(0,2))
        _hf = ("Segoe UI", 10, "bold")
        ttk.Label(header_frame, text="Ord", width=4, font=_hf).pack(side=tk.LEFT, padx=(0,4))
        ttk.Label(header_frame, text="Step#", width=5, font=_hf).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text="Object", width=20, font=_hf).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text="Type", width=8, font=_hf).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text="Action", width=18, font=_hf).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text="Parameters", font=_hf).pack(side=tk.LEFT, padx=2, fill="x", expand=True)
        ttk.Separator(self, orient="horizontal").pack(fill="x", padx=12)

        _style = ttk.Style(); _bg = _style.lookup('TFrame', 'background') or self["bg"]
        self.canvas_steps = tk.Canvas(self, borderwidth=0, background=_bg, highlightthickness=0)
        self.steps_area_frame = tk.Frame(self.canvas_steps, background=_bg)
        self.scrollbar_steps = tk.Scrollbar(self, orient="vertical", command=self.canvas_steps.yview)
        self.canvas_steps.configure(yscrollcommand=self.scrollbar_steps.set)
        self.scrollbar_steps.pack(side="right", fill="y", padx=(0,6), pady=6)
        self.canvas_steps.pack(side="left", fill="both", expand=True, padx=(6,0), pady=6)
        self.canvas_steps_window = self.canvas_steps.create_window((0,0), window=self.steps_area_frame, anchor="nw", tags="self.steps_area_frame")
        self.steps_area_frame.bind("<Configure>", lambda e: self.canvas_steps.configure(scrollregion=self.canvas_steps.bbox("all")))
        self.canvas_steps.bind("<Configure>", lambda e: self.canvas_steps.itemconfig(self.canvas_steps_window, width=e.width))
        
        self.canvas_steps.bind("<MouseWheel>", self._on_mousewheel)
        self.steps_area_frame.bind("<MouseWheel>", self._on_mousewheel)
        # Always scroll even when focus is on child widgets (Windows)
        self.bind_all("<MouseWheel>", self._on_mousewheel)
        # Linux scroll
        self.bind_all("<Button-4>", lambda e: self._on_mousewheel(type('evt', (), {'delta': 120})) )
        self.bind_all("<Button-5>", lambda e: self._on_mousewheel(type('evt', (), {'delta': -120})) )

        self.add_step_row(mark_modified=False)

        # Back/Close is now on the toolbar

    def _on_mousewheel(self, event):
        self.canvas_steps.yview_scroll(int(-1*(event.delta/120)), "units")

    def _back_to_main(self):
        if self.controller._check_unsaved_changes():
            self.controller.show_frame("MainFrame")

    def add_delay_between_rows(self, seconds=1.0):
        # Insert a delay after each non-delay row
        inserts = []
        for idx, entry in enumerate(list(self.step_widgets)):
            if entry["action_var"].get() != "Wait":
                inserts.append(idx + 1)
        offset = 0
        for pos in inserts:
            self.add_step_row(step_data={"object_name": None, "action": "Wait", "params": {"duration_s": float(seconds)}}, insert_at_index=pos + offset)
            offset += 1
        if inserts:
            self.controller.mark_sequence_modified()

    def add_step_row(self, step_data=None, insert_at_index=None, mark_modified=True):
        _style = ttk.Style(); _bg = _style.lookup('TFrame', 'background') or self.steps_area_frame.cget('bg')
        row_frame = ttk.Frame(self.steps_area_frame)
        row_frame.pack(fill="x", expand=True, pady=4, padx=6)

        order_btn_frame = ttk.Frame(row_frame)
        order_btn_frame.pack(side=tk.LEFT, padx=(2,0), fill="y")
        ttk.Button(order_btn_frame, text="▲", width=2, command=lambda idx=len(self.step_widgets): self.move_step_up(idx)).pack(pady=0)
        ttk.Button(order_btn_frame, text="▼", width=2, command=lambda idx=len(self.step_widgets): self.move_step_down(idx)).pack(pady=0)

        step_num_label = ttk.Label(row_frame, text="", width=4)
        step_num_label.pack(side=tk.LEFT, padx=2)

        obj_var = tk.StringVar(); action_var = tk.StringVar()
        obj_dropdown = ttk.Combobox(row_frame, textvariable=obj_var, values=self._get_object_display_names(), width=22, state="readonly")
        obj_dropdown.pack(side=tk.LEFT, padx=4)
        obj_type_label = ttk.Label(row_frame, text="", width=8)
        obj_type_label.pack(side=tk.LEFT, padx=2)
        action_dropdown = ttk.Combobox(row_frame, textvariable=action_var, width=18, state="readonly")
        action_dropdown.pack(side=tk.LEFT, padx=4)

        params_display_frame = ttk.Frame(row_frame)
        params_display_frame.pack(side=tk.LEFT, padx=3, fill="x", expand=True)

        params_edit_button = ttk.Button(row_frame, text="Edit")
        params_edit_button.pack(side=tk.LEFT, padx=3)
        # Quick add-delay (1.0s) after this row
        ttk.Button(row_frame, text="+1s", width=6, command=lambda rf=row_frame: self.insert_delay_after(self._index_of_row_frame(rf), 1.0)).pack(side=tk.LEFT, padx=2)
        del_button = ttk.Button(row_frame, text="✖", width=2, command=lambda rf=row_frame: self.delete_step_row_by_frame(rf))
        del_button.pack(side=tk.LEFT, padx=(3,2))

        current_step_entry = {
            "frame": row_frame, "obj_var": obj_var, "obj_dropdown": obj_dropdown,
            "action_var": action_var, "action_dropdown": action_dropdown,
            "params": {}, "params_button": params_edit_button, "delete_button": del_button,
            "step_num_label": step_num_label, "order_buttons": order_btn_frame,
            "params_display_frame": params_display_frame, "dynamic_param_widgets": {}
        }

        params_edit_button.config(command=lambda entry=current_step_entry: self.edit_step_params_dialog(entry))

        if insert_at_index is None:
            self.step_widgets.append(current_step_entry)
        else:
            self.step_widgets.insert(insert_at_index, current_step_entry)

        obj_var.trace_add("write", lambda *args, entry=current_step_entry: self.update_action_dropdown_and_params_ui(entry))
        action_var.trace_add("write", lambda *args, entry=current_step_entry: self.update_params_ui_for_action(entry))

        if step_data:
            current_step_entry["params"] = step_data.get("params", {}).copy()
            obj_val = step_data.get("object_name")
            obj_var.set(obj_val if obj_val else "(Global/Control)")
            action_var.set(step_data.get("action", ""))
        else:
            obj_var.set("(Global/Control)")
            if mark_modified and insert_at_index is None:
                self.controller.mark_sequence_modified()

        self._renumber_and_reorder_visuals()

    def _index_of_row_frame(self, rf):
        for i, entry in enumerate(self.step_widgets):
            if entry.get("frame") is rf:
                return i
        return len(self.step_widgets) - 1

    def insert_delay_after(self, index, seconds=1.0):
        if index is None:
            index = len(self.step_widgets) - 1
        step_data = {"object_name": None, "action": "Wait", "params": {"duration_s": float(seconds)}}
        # insert at index+1 (after current row)
        insert_at = min(index + 1, len(self.step_widgets))
        self.add_step_row(step_data=step_data, insert_at_index=insert_at)
        self.controller.mark_sequence_modified()

    def delete_step_row_by_frame(self, row_frame_to_delete):
        index_to_delete = -1
        for i, entry in enumerate(self.step_widgets):
            if entry["frame"] == row_frame_to_delete:
                index_to_delete = i
                break
        
        if index_to_delete != -1:
            self.step_widgets.pop(index_to_delete)["frame"].destroy()
            self.controller.mark_sequence_modified()
            self._renumber_and_reorder_visuals()
        self.steps_area_frame.update_idletasks()
        self.canvas_steps.config(scrollregion=self.canvas_steps.bbox("all"))

    def _renumber_and_reorder_visuals(self):
        for i, entry in enumerate(self.step_widgets):
            entry["step_num_label"].config(text=f"{i+1}.", font=("Segoe UI", 10, "bold"))
            up_button, down_button = entry["order_buttons"].winfo_children()
            try:
                up_button.config(text="▲", width=2, relief=tk.FLAT)
                down_button.config(text="▼", width=2, relief=tk.FLAT)
            except Exception:
                pass
            up_button.config(command=lambda current_idx=i: self.move_step_up(current_idx))
            down_button.config(command=lambda current_idx=i: self.move_step_down(current_idx))
            
            entry["frame"].pack_forget()
            entry["frame"].pack(fill="x", expand=True, pady=4, padx=6)

        self.steps_area_frame.update_idletasks()
        self.canvas_steps.config(scrollregion=self.canvas_steps.bbox("all"))

    def move_step_up(self, index):
        if index > 0:
            step = self.step_widgets.pop(index)
            self.step_widgets.insert(index - 1, step)
            self.controller.mark_sequence_modified()
            self._renumber_and_reorder_visuals()

    def move_step_down(self, index):
        if index < len(self.step_widgets) - 1:
            step = self.step_widgets.pop(index)
            self.step_widgets.insert(index + 1, step)
            self.controller.mark_sequence_modified()
            self._renumber_and_reorder_visuals()

    def update_action_dropdown_and_params_ui(self, step_entry):
        obj_var = step_entry["obj_var"]; action_dropdown = step_entry["action_dropdown"]
        selected_display = obj_var.get()
        selected_obj_name = self._name_from_display(selected_display)
        
        current_actions = []
        if selected_obj_name is None:
            current_actions.extend(self.ACTION_CONFIG["_global_"]); current_actions.extend(self.ACTION_CONFIG["_control_"])
            if step_entry.get("obj_type_label") is not None:
                step_entry["obj_type_label"].config(text="-")
        else:
            obj_data = self.controller.objects.get(selected_obj_name)
            if obj_data:
                obj_type = obj_data.get("type")
                obj_specific_actions = self.ACTION_CONFIG.get(obj_type, [])
                current_actions = obj_specific_actions + [ga for ga in self.ACTION_CONFIG["_global_"] if ga not in obj_specific_actions]
                if step_entry.get("obj_type_label") is not None:
                    step_entry["obj_type_label"].config(text=self._type_abbrev(obj_data))
        
        action_dropdown['values'] = sorted(list(set(current_actions)))
        
        current_action_val = step_entry["action_var"].get()
        if current_actions:
            if current_action_val not in current_actions:
                step_entry["action_var"].set(current_actions[0])
            else:
                self.update_params_ui_for_action(step_entry)
        else:
            step_entry["action_var"].set("")

    def update_params_ui_for_action(self, step_entry):
        for widget in step_entry["params_display_frame"].winfo_children(): widget.destroy()
        step_entry["dynamic_param_widgets"] = {}
        action = step_entry["action_var"].get(); params = step_entry["params"]
        frame = step_entry["params_display_frame"]
        step_entry["params_button"].pack_forget()

        def create_labeled_entry(parent, label_text, param_key, default_value="", width=8):
            ttk.Label(parent, text=label_text).pack(side=tk.LEFT, padx=(0,1))
            value = params.get(param_key, default_value)
            if value is None:
                value = default_value
            var = tk.StringVar(value=str(value))
            entry = tk.Entry(parent, textvariable=var, width=width)
            entry.pack(side=tk.LEFT, padx=(0,3)); step_entry["dynamic_param_widgets"][param_key] = var
            return var

        def create_labeled_combobox(parent, label_text, param_key, values_list, default_value="", width=10):
            ttk.Label(parent, text=label_text).pack(side=tk.LEFT, padx=(0,1))
            val = params.get(param_key, default_value)
            if val is None:
                val = ""
            vals = list(values_list)
            if val and val not in vals:
                vals.append(val)
            var = tk.StringVar(value=str(val) if vals else "")
            combo = ttk.Combobox(parent, textvariable=var, values=vals, width=width, state="readonly")
            combo.pack(side=tk.LEFT, padx=(0,3)); step_entry["dynamic_param_widgets"][param_key] = var
            return var

        if action == "Wait":
            create_labeled_entry(frame, "Duration(s):", "duration_s", 1.0, width=5); step_entry["params_button"].pack(side=tk.LEFT, padx=3)
        elif action == "Keyboard Input":
            create_labeled_entry(frame, "Text to Type:", "text_to_type", params.get("text_to_type",""), width=20)
            create_labeled_entry(frame, "Interval:", "interval", params.get("interval",0.01), width=4)
        elif action == "Press Key":
            create_labeled_combobox(frame, "Key:", "key_to_press", PYAUTOGUI_SPECIAL_KEYS, params.get("key_to_press", "enter"), width=12)
        elif action == "Hotkey Combo":
            create_labeled_combobox(frame, "Hotkey:", "selected_hotkey_name", PREDEFINED_HOTKEY_NAMES, params.get("selected_hotkey_name", PREDEFINED_HOTKEY_NAMES[0] if PREDEFINED_HOTKEY_NAMES else ""), width=30)
        elif action == "Click":
            step_entry["params_button"].pack(side=tk.LEFT, padx=3)
            if params: ttk.Label(frame, text=f"Btn:{params.get('button','L')}, Clicks:{params.get('clicks',1)}" ).pack(side=tk.LEFT)
        elif action == "Scroll":
            step_entry["params_button"].pack(side=tk.LEFT, padx=3)
            if params: ttk.Label(frame, text=f"Dir:{params.get('direction','Down')}, Amt:{params.get('amount',10)}" ).pack(side=tk.LEFT)
        elif action == "Wait for Image":
            create_labeled_entry(frame, "Timeout:", "timeout_s", 10, width=4)
            create_labeled_entry(frame, "Conf:", "confidence", params.get("confidence", self.controller.objects.get(self._name_from_display(step_entry["obj_var"].get()), {}).get("confidence",0.8)), width=4)
        elif action == "Wait for Pixel Color":
            create_labeled_entry(frame, "Timeout:", "timeout_s", 10, width=4); step_entry["params_button"].pack(side=tk.LEFT, padx=3)
        elif action == "Goto Step":
            create_labeled_entry(frame, "Target Step#:", "target_step", 1, width=4)
        elif action == "If Image Found":
            ttk.Label(frame, text="If Obj:").pack(side=tk.LEFT, padx=(0,1))
            cond_names = self.controller.get_object_names(object_type="image")
            default_cond = params.get("condition_object_name", "")
            if default_cond and default_cond not in cond_names:
                cond_names.append(default_cond)
            cond_obj_var = tk.StringVar(value=default_cond)
            cond_obj_combo = ttk.Combobox(frame, textvariable=cond_obj_var, values=cond_names, width=10, state="readonly")
            cond_obj_combo.pack(side=tk.LEFT, padx=(0,2)); step_entry["dynamic_param_widgets"]["condition_object_name"] = cond_obj_var
            create_labeled_entry(frame, "Then#:", "then_step", 1, width=3)
            create_labeled_entry(frame, "Else#:", "else_step", "Next", width=4)
            create_labeled_entry(frame, "Conf:", "confidence", params.get("confidence",0.8), width=3)
        elif action == "If Pixel Color":
            ttk.Label(frame, text="If Obj:").pack(side=tk.LEFT, padx=(0,1))
            cond_names = self.controller.get_object_names(object_type="pixel")
            default_cond = params.get("condition_object_name", "")
            if default_cond and default_cond not in cond_names:
                cond_names.append(default_cond)
            cond_obj_var = tk.StringVar(value=default_cond)
            cond_obj_combo = ttk.Combobox(frame, textvariable=cond_obj_var, values=cond_names, width=10, state="readonly")
            cond_obj_combo.pack(side=tk.LEFT, padx=(0,2)); step_entry["dynamic_param_widgets"]["condition_object_name"] = cond_obj_var
            create_labeled_entry(frame, "Then#:", "then_step", 1, width=3)
            create_labeled_entry(frame, "Else#:", "else_step", "Next", width=4)
            step_entry["params_button"].pack(side=tk.LEFT, padx=3)

        # Always show a small note field at the end
        try:
            ttk.Label(frame, text="Note:").pack(side=tk.LEFT, padx=(6,2))
            from tkinter import scrolledtext as _st
            existing = step_entry.get("note_widget")
            if existing and existing.winfo_exists():
                existing.destroy()
            note_widget = _st.ScrolledText(frame, width=30, height=2, wrap=tk.WORD)
            note_text = step_entry.get("note_var").get() if isinstance(step_entry.get("note_var"), tk.StringVar) else str(step_entry.get("params", {}).get("note", ""))
            note_widget.insert(tk.INSERT, note_text)
            step_entry["note_widget"] = note_widget
            note_widget.pack(side=tk.LEFT, padx=(0,3))
        except Exception:
            pass

    def edit_step_params_dialog(self, step_entry):
        action = step_entry["action_var"].get(); obj_name = self._name_from_display(step_entry["obj_var"].get())
        current_params = step_entry["params"]; dialog_made_change = False; dialog = None
        if action == "Click": dialog = ClickParamsDialog(self, "Click Action Parameters", current_params.copy())
        elif action == "Wait": dialog = WaitParamsDialog(self, "Wait Action Parameters", current_params.copy())
        elif action == "Scroll": dialog = ScrollParamsDialog(self, "Scroll Action Parameters", current_params.copy())
        elif action == "Wait for Pixel Color":
            target_pixel_obj = self.controller.objects.get(obj_name)
            dialog = PixelColorWaitParamsDialog(self, "Pixel Color Wait Parameters", current_params.copy(), target_pixel_obj)
        elif action == "Wait for Image": simpledialog.messagebox.showinfo("Info","Parameters for 'Wait for Image' are set inline.", parent=self); return
        elif action == "If Pixel Color":
            target_pixel_obj = self.controller.objects.get(step_entry["dynamic_param_widgets"]["condition_object_name"].get())
            dialog = PixelColorWaitParamsDialog(self, "Set Expected RGB for If Pixel Color", current_params.copy(), target_pixel_obj, for_if_condition=True)
        if dialog:
            if dialog.result is not None:
                if dialog.result != current_params:
                    step_entry["params"] = dialog.result; dialog_made_change = True
                    self.controller.mark_sequence_modified()
                print(f"Params for step (action: {action}): {step_entry['params']}")
        if dialog_made_change: self.update_params_ui_for_action(step_entry)

    def refresh_content(self): self.clear_and_rebuild_steps(self.controller.current_steps)
    def refresh_object_dropdowns(self):
        all_display = self._get_object_display_names()
        for step_entry in self.step_widgets:
            current_display = step_entry["obj_var"].get()
            base_name = self._name_from_display(current_display)
            step_entry["obj_dropdown"]["values"] = all_display
            # Rebuild a correct display string if base exists
            if base_name is None:
                step_entry["obj_var"].set("(Global/Control)")
            elif base_name in self.controller.objects:
                step_entry["obj_var"].set(self._display_name_for_object(base_name))
            else:
                step_entry["obj_var"].set("(Global/Control)")
            self.update_action_dropdown_and_params_ui(step_entry)

    def finalize_steps_for_controller(self):
        self.controller.current_steps = []
        for _, sw_entry in enumerate(self.step_widgets):
            obj_display = sw_entry["obj_var"].get(); action = sw_entry["action_var"].get()
            obj_name = self._name_from_display(obj_display)
            final_params = sw_entry["params"].copy()
            for param_key, str_var_widget in sw_entry.get("dynamic_param_widgets", {}).items():
                value = str_var_widget.get()
                if param_key in ["duration_s", "timeout_s", "confidence", "interval"]:
                    try: final_params[param_key] = float(value)
                    except ValueError: final_params[param_key] = value
                elif param_key in ["target_step", "then_step", "else_step", "amount"]:
                    try:
                        if value.lower() == "next" and param_key == "else_step": final_params[param_key] = None
                        elif value == "":
                            if param_key in ["then_step", "else_step"]: final_params[param_key] = None
                            else: final_params[param_key] = value
                        else: final_params[param_key] = int(value)
                    except ValueError: final_params[param_key] = value
                else: final_params[param_key] = value
            if action:
                note_text = ""
                try:
                    nw = sw_entry.get("note_widget")
                    if nw is not None and nw.winfo_exists():
                        note_text = nw.get('1.0', tk.END).strip()
                    else:
                        note_text = sw_entry.get("note_var", tk.StringVar(value="")).get()
                except Exception:
                    note_text = sw_entry.get("note_var", tk.StringVar(value="")).get()
                self.controller.current_steps.append({
                    "object_name": obj_name if obj_name is not None else None,
                    "action": action,
                    "params": final_params,
                    "note": note_text
                })
        print("Finalized steps for controller:", self.controller.current_steps)

    def clear_and_rebuild_steps(self, steps_data_list_from_file):
        for widget_entry in self.step_widgets:
            if widget_entry["frame"].winfo_exists(): widget_entry["frame"].destroy()
        self.step_widgets = []
        self.controller.current_steps = list(steps_data_list_from_file) if steps_data_list_from_file else []
        for step_data in self.controller.current_steps:
            self.add_step_row(step_data)
        if not self.step_widgets: self.add_step_row()
        self._renumber_and_reorder_visuals()
        self.controller.mark_sequence_modified(False)


class InstructionsFrame(BaseFrame):
    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        tk.Label(self, text="Instructions", font=("Arial", 16, "bold"), bg=self["bg"], fg="white").pack(pady=10)
        instructions_text = """
Welcome to the Python Desktop Automation Tool!

**1. Core Concepts**
   - **Objects** represent Regions, Images, or Pixels on screen.
   - **Steps** act on Objects or perform global actions.
   - **Sequences** are ordered lists of Steps that can loop.

**2. Main Menu**
   - **New Sequence** clears current work.
   - **Instructions** shows this help.
   - **Object Creation** defines screen elements.
   - **Step Creator** builds the automation sequence.
   - **File Operations** load or save sequences and assets.
   - **Loops** set how many times the sequence repeats (0 = infinite).
   - **Run Sequence** executes the steps.

**3. Object Creation Menu**
   - Unique names for all objects.
   - **Region/Image Creation** via grid or drag capture.
   - **Pixel Monitor** captures RGB at a point.
   - All created objects are listed for quick review.

**4. Step Creator Menu**
   - Toolbar for adding steps or saving.
   - **Quick +1s** button inserts delay after a step.
   - Each step supports optional **notes**.
   - Actions include **Click**, **Scroll**, **Keyboard Input**, **Press Key**, **Hotkey Combo**, and logic like **Goto**, **If Image Found**, or **If Pixel Color**.
   - Use the arrows to reorder steps.

**5. Running & Saving**
   - Move mouse to top-left to abort (failsafe).
   - Window title shows "*" when sequence is modified.

**Tips**
   - Save and test often.
   - Descriptive names make sequences clearer.
"""
        text_area = scrolledtext.ScrolledText(self, wrap=tk.WORD, height=20, width=70, font=("Arial", 9), bg="#222222", fg="white", insertbackground="white")
        text_area.insert(tk.INSERT, instructions_text)
        text_area.config(state=tk.DISABLED, bg="#222222", fg="white", relief=tk.FLAT, borderwidth=0)
        text_area.pack(pady=10, padx=10, fill="both", expand=True)
        tk.Button(self, text="Back to Main Menu", command=lambda: controller.show_frame("MainFrame"), bg="#444444", fg="white").pack(pady=10)


# --- Parameter Dialogs for Steps ---
class BaseParamsDialog(simpledialog.Dialog):
    def __init__(self, parent, title, existing_params=None):
        self.existing_params = existing_params if existing_params else {}
        self.result = None
        super().__init__(parent, title)

class ClickParamsDialog(BaseParamsDialog):
    def body(self, master):
        tk.Label(master, text="Button:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        self.button_var = tk.StringVar(value=self.existing_params.get("button", "left"))
        self.button_menu = ttk.Combobox(master, textvariable=self.button_var, values=["left", "right", "middle"], state="readonly", width=10)
        self.button_menu.grid(row=0, column=1, columnspan=2, sticky="ew", padx=5, pady=2)
        tk.Label(master, text="Clicks:").grid(row=1, column=0, sticky="w", padx=5, pady=2)
        self.clicks_var = tk.IntVar(value=self.existing_params.get("clicks", 1))
        self.clicks_menu = ttk.Combobox(master, textvariable=self.clicks_var, values=[1, 2, 3], state="readonly", width=5)
        self.clicks_menu.grid(row=1, column=1, sticky="w", padx=5, pady=2)
        tk.Label(master, text="Interval (s):").grid(row=2, column=0, sticky="w", padx=5, pady=2)
        self.interval_var = tk.StringVar(value=str(self.existing_params.get("interval", 0.1)))
        self.interval_entry = tk.Entry(master, textvariable=self.interval_var, width=7)
        self.interval_entry.grid(row=2, column=1, sticky="w", padx=5, pady=2)
        tk.Label(master, text="(for double/triple)").grid(row=2, column=2, sticky="w", padx=5, pady=2)
        self.clicks_var.trace_add("write", self.toggle_interval_field); self.toggle_interval_field()
        return self.button_menu
    def toggle_interval_field(self, *args):
        try: self.interval_entry.config(state="normal" if self.clicks_var.get()>1 else "disabled")
        except tk.TclError: pass
    def validate(self):
        try:
            clicks=self.clicks_var.get();
            if clicks not in [1,2,3]: raise ValueError("Clicks must be 1, 2, or 3.")
            if clicks>1 and float(self.interval_var.get())<0: raise ValueError("Interval must be non-negative.")
            return 1
        except (ValueError,tk.TclError) as e: simpledialog.messagebox.showerror("Invalid Input",str(e),parent=self); return 0
    def apply(self):
        self.result={"button":self.button_var.get(),"clicks":self.clicks_var.get()}
        if self.result["clicks"]>1: self.result["interval"]=float(self.interval_var.get())
        else: self.result["interval"]=0.0

class ScrollParamsDialog(BaseParamsDialog):
    def body(self, master):
        tk.Label(master,text="Direction:").grid(row=0,column=0,sticky="w",padx=5,pady=2)
        self.direction_var=tk.StringVar(value=self.existing_params.get("direction","down"))
        self.direction_menu=ttk.Combobox(master,textvariable=self.direction_var,values=["up","down","left","right"],state="readonly",width=10)
        self.direction_menu.grid(row=0,column=1,sticky="ew",padx=5,pady=2)
        tk.Label(master,text="Amount:").grid(row=1,column=0,sticky="w",padx=5,pady=2)
        self.amount_var=tk.IntVar(value=self.existing_params.get("amount",10))
        self.amount_entry=tk.Entry(master,textvariable=self.amount_var,width=7)
        self.amount_entry.grid(row=1,column=1,sticky="w",padx=5,pady=2)
        tk.Label(master,text="(clicks/units)").grid(row=1,column=2,sticky="w",padx=5,pady=2)
        tk.Label(master,text="Scroll At (optional):").grid(row=2,column=0,sticky="w",padx=5,pady=2)
        tk.Label(master,text="X:").grid(row=3,column=0,sticky="e",padx=5,pady=2)
        self.x_var=tk.StringVar(value=str(self.existing_params.get("x","")))
        self.x_entry=tk.Entry(master,textvariable=self.x_var,width=7)
        self.x_entry.grid(row=3,column=1,sticky="w",padx=5,pady=2)
        tk.Label(master,text="Y:").grid(row=4,column=0,sticky="e",padx=5,pady=2)
        self.y_var=tk.StringVar(value=str(self.existing_params.get("y","")))
        self.y_entry=tk.Entry(master,textvariable=self.y_var,width=7)
        self.y_entry.grid(row=4,column=1,sticky="w",padx=5,pady=2)
        tk.Label(master,text="(If blank, scrolls at mouse pos)").grid(row=5,columnspan=3,sticky="w",padx=5,pady=2)
        return self.direction_menu
    def validate(self):
        try:
            amount=self.amount_var.get()
            if not isinstance(amount,int) or amount==0: raise ValueError("Scroll amount must be non-zero integer.")
            x_str,y_str=self.x_var.get(),self.y_var.get()
            if (x_str and not y_str) or (y_str and not x_str): raise ValueError("If specifying coords, both X and Y needed.")
            if x_str: int(x_str);
            if y_str: int(y_str)
            return 1
        except (ValueError,tk.TclError) as e: simpledialog.messagebox.showerror("Invalid Input",str(e),parent=self); return 0
    def apply(self):
        self.result={"direction":self.direction_var.get(),"amount":self.amount_var.get()}
        x_str,y_str=self.x_var.get(),self.y_var.get()
        if x_str and y_str: self.result["x"]=int(x_str); self.result["y"]=int(y_str)

class WaitParamsDialog(BaseParamsDialog):
    def body(self, master):
        self.wait_type_var=tk.StringVar(value=self.existing_params.get("type","static"))
        self.duration_var=tk.StringVar(value=str(self.existing_params.get("duration_s",1.0)))
        self.min_dur_var=tk.StringVar(value=str(self.existing_params.get("min_s",0.5)))
        self.max_dur_var=tk.StringVar(value=str(self.existing_params.get("max_s",2.0)))
        tk.Radiobutton(master,text="Static Wait (s):",variable=self.wait_type_var,value="static",command=self.toggle_fields).grid(row=0,column=0,sticky="w")
        self.static_entry=tk.Entry(master,textvariable=self.duration_var,width=10); self.static_entry.grid(row=0,column=1)
        tk.Radiobutton(master,text="Random Wait (min-max s):",variable=self.wait_type_var,value="random",command=self.toggle_fields).grid(row=1,column=0,sticky="w")
        self.min_entry=tk.Entry(master,textvariable=self.min_dur_var,width=5); self.min_entry.grid(row=1,column=1,sticky="w")
        tk.Label(master,text="to").grid(row=1,column=1)
        self.max_entry=tk.Entry(master,textvariable=self.max_dur_var,width=5); self.max_entry.grid(row=1,column=1,sticky="e")
        self.toggle_fields(); return self.static_entry
    def toggle_fields(self):
        is_static = self.wait_type_var.get()=="static"
        self.static_entry.config(state="normal" if is_static else "disabled")
        self.min_entry.config(state="disabled" if is_static else "normal")
        self.max_entry.config(state="disabled" if is_static else "normal")
    def validate(self):
        try:
            if self.wait_type_var.get()=="static":
                if float(self.duration_var.get())<0: raise ValueError("Duration non-negative.")
            else:
                min_v,max_v=float(self.min_dur_var.get()),float(self.max_dur_var.get())
                if min_v<0 or max_v<0: raise ValueError("Durations non-negative.")
                if min_v>max_v: raise ValueError("Min <= Max.")
            return 1
        except (ValueError,tk.TclError) as e: simpledialog.messagebox.showerror("Invalid Input",str(e),parent=self); return 0
    def apply(self):
        if self.wait_type_var.get()=="static": self.result={"type":"static","duration_s":float(self.duration_var.get())}
        else: self.result={"type":"random","min_s":float(self.min_dur_var.get()),"max_s":float(self.max_dur_var.get())}

class KeyboardParamsDialog(BaseParamsDialog):
    def body(self, master):
        tk.Label(master,text="Text to type:").grid(row=0,column=0,sticky="w")
        self.text_var=tk.StringVar(value=self.existing_params.get("text_to_type",""))
        self.text_entry=tk.Entry(master,textvariable=self.text_var,width=30); self.text_entry.grid(row=0,column=1,padx=5,pady=5)
        tk.Label(master,text="Special Keys (e.g. enter, ctrl,c):").grid(row=1,column=0,sticky="w")
        keys_val = self.existing_params.get("keys_to_press",[])
        keys_str = ", ".join(keys_val) if isinstance(keys_val,list) else str(keys_val)
        self.keys_var=tk.StringVar(value=keys_str)
        self.keys_entry=tk.Entry(master,textvariable=self.keys_var,width=30); self.keys_entry.grid(row=1,column=1,padx=5,pady=5)
        tk.Label(master,text="(Comma-separate for hotkeys)").grid(row=2,columnspan=2,sticky="w",padx=5)
        return self.text_entry
    def apply(self):
        self.result={}; text_val=self.text_var.get(); keys_val_str=self.keys_var.get()
        if text_val: self.result["text_to_type"]=text_val
        if keys_val_str:
            if ',' in keys_val_str: self.result["keys_to_press"]=[k.strip() for k in keys_val_str.split(',')]
            else: self.result["keys_to_press"]=keys_val_str.strip()

class PixelColorWaitParamsDialog(BaseParamsDialog):
    def __init__(self, parent, title, existing_params=None, pixel_obj=None, for_if_condition=False):
        self.pixel_obj = pixel_obj
        self.for_if_condition = for_if_condition
        super().__init__(parent, title, existing_params)

    def body(self, master):
        default_rgb_str = ""
        if self.existing_params.get("expected_rgb"): default_rgb_str = ",".join(map(str, self.existing_params["expected_rgb"]))
        elif self.pixel_obj and self.pixel_obj.get("rgb"): default_rgb_str = ",".join(map(str, self.pixel_obj["rgb"]))
        
        tk.Label(master,text="Expected RGB (R,G,B):").grid(row=0,column=0,sticky="w")
        self.rgb_var=tk.StringVar(value=default_rgb_str)
        self.rgb_entry=tk.Entry(master,textvariable=self.rgb_var,width=15); self.rgb_entry.grid(row=0,column=1)
        tk.Button(master,text="Pick Color",command=self.pick_color).grid(row=0,column=2,padx=5)

        if not self.for_if_condition:
            tk.Label(master,text="Timeout (s):").grid(row=1,column=0,sticky="w")
            self.timeout_var=tk.StringVar(value=str(self.existing_params.get("timeout_s",10.0)))
            self.timeout_entry=tk.Entry(master,textvariable=self.timeout_var,width=10); self.timeout_entry.grid(row=1,column=1)
        return self.rgb_entry
    def pick_color(self):
        initial_color_hex=None
        try: r,g,b=map(int,self.rgb_var.get().split(',')); initial_color_hex=f"#{r:02x}{g:02x}{b:02x}"
        except: pass
        color_code=colorchooser.askcolor(title="Choose Expected Pixel Color",initialcolor=initial_color_hex,parent=self)
        if color_code and color_code[0]: r,g,b=map(int,color_code[0]); self.rgb_var.set(f"{r},{g},{b}")
    def validate(self):
        try:
            rgb_parts=[int(p.strip()) for p in self.rgb_var.get().split(',')]
            if len(rgb_parts)!=3 or not all(0<=v<=255 for v in rgb_parts): raise ValueError("RGB: 3 numbers 0-255, comma-sep.")
            if not self.for_if_condition and float(self.timeout_var.get())<0: raise ValueError("Timeout non-negative.")
            return 1
        except (ValueError,tk.TclError) as e: simpledialog.messagebox.showerror("Invalid Input",str(e),parent=self); return 0
    def apply(self):
        rgb_parts=[int(p.strip()) for p in self.rgb_var.get().split(',')]
        self.result = self.existing_params.copy()
        self.result["expected_rgb"] = tuple(rgb_parts)
        if not self.for_if_condition: self.result["timeout_s"] = float(self.timeout_var.get())

class ImageWaitParamsDialog(BaseParamsDialog):
    def __init__(self, parent, title, existing_params=None, image_obj=None):
        self.image_obj = image_obj
        super().__init__(parent, title, existing_params)
    def body(self, master):
        default_conf=0.8
        if self.existing_params.get("confidence"): default_conf=self.existing_params["confidence"]
        elif self.image_obj and self.image_obj.get("confidence"): default_conf=self.image_obj["confidence"]
        tk.Label(master,text="Confidence (0.0-1.0):").grid(row=0,column=0,sticky="w")
        self.confidence_var=tk.StringVar(value=str(default_conf))
        self.confidence_entry=tk.Entry(master,textvariable=self.confidence_var,width=10); self.confidence_entry.grid(row=0,column=1)
        tk.Label(master,text="Timeout (s):").grid(row=1,column=0,sticky="w")
        self.timeout_var=tk.StringVar(value=str(self.existing_params.get("timeout_s",10.0)))
        self.timeout_entry=tk.Entry(master,textvariable=self.timeout_var,width=10); self.timeout_entry.grid(row=1,column=1)
        return self.confidence_entry
    def validate(self):
        try:
            conf=float(self.confidence_var.get())
            if not (0.0<=conf<=1.0): raise ValueError("Confidence 0.0-1.0.")
            if float(self.timeout_var.get())<0: raise ValueError("Timeout non-negative.")
            return 1
        except (ValueError,tk.TclError) as e: simpledialog.messagebox.showerror("Invalid Input",str(e),parent=self); return 0
    def apply(self): self.result={"confidence":float(self.confidence_var.get()),"timeout_s":float(self.timeout_var.get())}


# --- Main Execution ---
if __name__ == "__main__":
    try:
        app_root = tk.Tk()
        app_instance = DesktopAutomationApp(app_root)
        if hasattr(app_instance.frames["StepCreatorFrame"], 'finalize_steps_for_controller'):
            app_instance.frames["StepCreatorFrame"].finalize_steps_for_controller()
        app_root.mainloop()
    except Exception as e:
        # Best-effort startup logging
        try:
            os.makedirs('logs', exist_ok=True)
            with open(os.path.join('logs', 'startup_error.log'), 'a', encoding='utf-8') as f:
                import traceback
                f.write("\n=== Startup Error ===\n")
                traceback.print_exc(file=f)
        except Exception:
            pass
        raise





