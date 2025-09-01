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

        self.objects = {}
        self.current_steps = []
        self.current_project_path = None
        self.current_sequence_name = DEFAULT_PROJECT_NAME
        self.loop_count = tk.IntVar(value=1)
        self.sequence_modified = False

        self.grid_window = None
        self.grid_rows_var = tk.IntVar(value=10)
        self.grid_cols_var = tk.IntVar(value=10)
        self.selected_grid_cells = []

        self.drag_select_window = None
        self.drag_start_x = None
        self.drag_start_y = None
        self.drag_rect_id = None

        self.pixel_monitor_active = False
        self._pixel_listener = None

        self.container = tk.Frame(root)
        self.container.pack(fill="both", expand=True)

        self.frames = {}
        for F in (MainFrame, ObjectCreationFrame, StepCreatorFrame, InstructionsFrame):
            page_name = F.__name__
            frame = F(parent=self.container, controller=self)
            self.frames[page_name] = frame
            frame.grid(row=0, column=0, sticky="nsew")

        self.show_frame("MainFrame")

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
        if self.frames["StepCreatorFrame"].winfo_exists():
             self.frames["StepCreatorFrame"].refresh_object_dropdowns()
        self.mark_sequence_modified()
        return True

    def _start_pixel_monitor_listener(self):
        if self.pixel_monitor_active:
            return
        self.pixel_monitor_active = True

        self.pixel_capture_instruction_window = tk.Toplevel(self.root)
        self.pixel_capture_instruction_window.attributes('-topmost', True)
        self.pixel_capture_instruction_window.geometry("300x100+100+100")
        tk.Label(self.pixel_capture_instruction_window,
                 text="Pixel Monitor Active\nClick anywhere on your primary screen to select a pixel.\nPress ESC in this small window to cancel.").pack(pady=20)
        self.pixel_capture_instruction_window.focus_force()

        def _on_pixel_capture_escape(event=None):
            self.pixel_monitor_active = False
            if self.pixel_capture_instruction_window and self.pixel_capture_instruction_window.winfo_exists():
                self.pixel_capture_instruction_window.destroy()
            print("Pixel monitoring cancelled.")

        self.pixel_capture_instruction_window.bind("<Escape>", _on_pixel_capture_escape)

        tk.Button(self.pixel_capture_instruction_window, text="Capture Pixel Under Mouse NOW",
                  command=self._capture_pixel_under_mouse).pack(pady=5)

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

    def create_region_grid_mode(self):
        if self.grid_window and self.grid_window.winfo_exists(): self.grid_window.destroy()
        self.grid_window = tk.Toplevel(self.root)
        self.grid_window.attributes('-fullscreen', True); self.grid_window.attributes('-alpha', 0.4); self.grid_window.attributes('-topmost', True)
        self.grid_canvas = tk.Canvas(self.grid_window, bg='gray', highlightthickness=0); self.grid_canvas.pack(fill="both", expand=True)
        self.screen_width = self.root.winfo_screenwidth(); self.screen_height = self.root.winfo_screenheight()
        try:
            rows = self.grid_rows_var.get(); cols = self.grid_cols_var.get()
            if rows <= 0 or cols <= 0: raise ValueError("Grid dimensions must be positive.")
        except (tk.TclError, ValueError) as e:
            simpledialog.messagebox.showerror("Error", f"Invalid grid dimensions: {e}. Using 10x10.", parent=self.root)
            self.grid_rows_var.set(10); self.grid_cols_var.set(10); rows, cols = 10, 10
        self.cell_width = self.screen_width / cols; self.cell_height = self.screen_height / rows
        self.selected_grid_cells = []; self._draw_grid_on_canvas()
        self.grid_canvas.bind("<Button-1>", self._on_grid_cell_click)
        self.grid_window.bind("<Escape>", lambda e: self._confirm_grid_selection(cancelled=True))
        confirm_bar = tk.Frame(self.grid_canvas, bg="lightgray", relief=tk.RAISED, borderwidth=1)
        tk.Label(confirm_bar, text=f"{rows}x{cols} Grid. Click cells. ESC to cancel.", bg="lightgray").pack(side=tk.LEFT, padx=10)
        tk.Button(confirm_bar, text="Confirm Selection", command=self._confirm_grid_selection).pack(side=tk.LEFT, padx=10)
        self.grid_canvas.create_window(self.screen_width // 2, 30, window=confirm_bar, anchor="n")
        self.grid_window.focus_force()

    def _draw_grid_on_canvas(self):
        self.grid_canvas.delete("grid_line"); self.grid_canvas.delete("cell_highlight")
        rows = self.grid_rows_var.get(); cols = self.grid_cols_var.get()
        for r in range(rows):
            for c in range(cols):
                x1, y1 = c * self.cell_width, r * self.cell_height; x2, y2 = x1 + self.cell_width, y1 + self.cell_height
                if (r,c) in self.selected_grid_cells: self.grid_canvas.create_rectangle(x1, y1, x2, y2, fill="blue", outline="lightblue", stipple="gray50", tags="cell_highlight")
                if r < rows: self.grid_canvas.create_line(0, y2, self.screen_width, y2, fill="white", tags="grid_line", width=0.5)
                if c < cols: self.grid_canvas.create_line(x2, 0, x2, self.screen_height, fill="white", tags="grid_line", width=0.5)

    def _on_grid_cell_click(self, event):
        col = int(event.x // self.cell_width); row = int(event.y // self.cell_height); cell = (row, col)
        if cell in self.selected_grid_cells: self.selected_grid_cells.remove(cell)
        else: self.selected_grid_cells.append(cell)
        self._draw_grid_on_canvas()

    def _confirm_grid_selection(self, cancelled=False):
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

    def create_region_drag_mode(self):
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
            creation_type = self.frames["ObjectCreationFrame"].current_creation_type
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
        self.configure(bg="#E0E0E0")

class MainFrame(BaseFrame):
    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        tk.Label(self, text="Automation Tool", font=("Arial", 16, "bold"), bg=self["bg"]).pack(pady=10)
        btn_frame_new = tk.Frame(self, bg=self["bg"]); btn_frame_new.pack(pady=5, fill="x", padx=20)
        tk.Button(btn_frame_new, text="New Sequence", width=20, command=controller.new_sequence).pack(pady=3, fill="x")
        tk.Button(btn_frame_new, text="Instructions", width=20, command=lambda: controller.show_frame("InstructionsFrame")).pack(pady=3, fill="x")

        tk.Label(btn_frame_new, text="Create & Edit", font=("Arial", 12, "underline"), bg=self["bg"]).pack(pady=(8,0))
        tk.Button(btn_frame_new, text="Object Creation", width=20, command=lambda: controller.show_frame("ObjectCreationFrame")).pack(pady=3, fill="x")
        tk.Button(btn_frame_new, text="Step Creator", width=20, command=lambda: controller.show_frame("StepCreatorFrame")).pack(pady=3, fill="x")

        ttk.Separator(self, orient="horizontal").pack(fill="x", pady=10, padx=20)

        tk.Label(self, text="File Operations", font=("Arial", 12, "underline"), bg=self["bg"]).pack(pady=(8,0))
        file_ops_frame = tk.Frame(self,bg=self["bg"]); file_ops_frame.pack(pady=5,padx=20,fill="x")
        tk.Button(file_ops_frame, text="Load Sequence", command=controller.load_sequence).pack(side=tk.LEFT, expand=True, fill="x", padx=(0,3))
        tk.Button(file_ops_frame, text="Save Sequence As...", command=controller.save_sequence_as).pack(side=tk.LEFT, expand=True, fill="x", padx=(3,0))

        loaded_seq_frame = tk.Frame(self,bg=self["bg"]); loaded_seq_frame.pack(pady=5,padx=20,fill="x")
        tk.Label(loaded_seq_frame,text="Current:",bg=self["bg"]).pack(side=tk.LEFT)
        self.loaded_seq_label = tk.Label(loaded_seq_frame,text="No sequence loaded",bg="white",relief=tk.SUNKEN,anchor="w"); self.loaded_seq_label.pack(side=tk.LEFT,expand=True,fill="x")

        loop_frame = tk.Frame(self,bg=self["bg"]); loop_frame.pack(pady=8,padx=20,fill="x")
        tk.Label(loop_frame,text="Loops (0=inf):",bg=self["bg"]).pack(side=tk.LEFT)
        tk.Entry(loop_frame,textvariable=controller.loop_count,width=5,justify="center").pack(side=tk.LEFT,padx=5)

        tk.Button(self,text="Run Sequence",width=20,font=("Arial",12,"bold"),bg="#A5D6A7",command=controller.run_sequence).pack(pady=15,padx=20,fill="x")

    def refresh_content(self):
        if self.controller.current_sequence_name == DEFAULT_PROJECT_NAME and not self.controller.current_project_path:
            self.loaded_seq_label.config(text="No sequence loaded")
        else:
            self.loaded_seq_label.config(text=self.controller.current_sequence_name)


class ObjectCreationFrame(BaseFrame):
    def __init__(self, parent, controller):
        super().__init__(parent, controller)
        self.current_creation_type = "region"
        tk.Label(self, text="Object Creation", font=("Arial", 16, "bold"), bg=self["bg"]).pack(pady=10)
        region_frame = tk.LabelFrame(self,text="Region Creation",padx=10,pady=10,bg=self["bg"]); region_frame.pack(pady=5,padx=10,fill="x")
        grid_dim_frame = tk.Frame(region_frame,bg=self["bg"]); grid_dim_frame.pack(fill="x")
        tk.Label(grid_dim_frame,text="Grid (W x H):",bg=self["bg"]).pack(side=tk.LEFT,padx=(0,2))
        tk.Entry(grid_dim_frame,textvariable=controller.grid_cols_var,width=3).pack(side=tk.LEFT)
        tk.Label(grid_dim_frame,text="x",bg=self["bg"]).pack(side=tk.LEFT,padx=1)
        tk.Entry(grid_dim_frame,textvariable=controller.grid_rows_var,width=3).pack(side=tk.LEFT,padx=(0,5))
        tk.Button(grid_dim_frame,text="Grid Mode",command=lambda:self.set_creation_type_and_run("region",controller.create_region_grid_mode)).pack(side=tk.LEFT,expand=True,fill="x")
        tk.Button(region_frame,text="Drag Mode",command=lambda:self.set_creation_type_and_run("region",controller.create_region_drag_mode)).pack(pady=3,fill="x")
        tk.Button(region_frame,text="Pixel Monitor",command=controller._start_pixel_monitor_listener).pack(pady=3,fill="x")
        image_frame = tk.LabelFrame(self,text="Image Creation",padx=10,pady=10,bg=self["bg"]); image_frame.pack(pady=5,padx=10,fill="x")
        tk.Button(image_frame,text="Grid Mode (Capture)",command=lambda:self.set_creation_type_and_run("image",controller.create_region_grid_mode)).pack(pady=3,fill="x")
        tk.Button(image_frame,text="Drag Mode (Capture)",command=lambda:self.set_creation_type_and_run("image",controller.create_region_drag_mode)).pack(pady=3,fill="x")
        sound_frame = tk.LabelFrame(self,text="Sound Creation (Future)",padx=10,pady=10,bg=self["bg"]); sound_frame.pack(pady=5,padx=10,fill="x")
        tk.Button(sound_frame,text="Sound Recording",state=tk.DISABLED).pack(pady=3,fill="x")
        self.objects_list_frame=tk.LabelFrame(self,text="Created Objects",padx=10,pady=10,bg=self["bg"]); self.objects_list_frame.pack(pady=5,padx=10,fill="both",expand=True)
        self.objects_text=scrolledtext.ScrolledText(self.objects_list_frame,height=4,wrap=tk.WORD,state=tk.DISABLED); self.objects_text.pack(fill="both",expand=True)
        tk.Button(self,text="Back to Main Menu",command=lambda:controller.show_frame("MainFrame")).pack(pady=10,side=tk.BOTTOM)
    def set_creation_type_and_run(self,c_type,func_to_run): self.current_creation_type=c_type; func_to_run()
    def update_objects_display(self):
        self.objects_text.config(state=tk.NORMAL); self.objects_text.delete(1.0,tk.END)
        if not self.controller.objects: self.objects_text.insert(tk.END,"No objects created yet.")
        else:
            for name,data in self.controller.objects.items():
                obj_type=data.get("type","N/A"); details=""
                if obj_type=="region" or obj_type=="image": details=f"Coords: {data.get('coords')}"
                if obj_type=="image" and data.get('image_path'): details+=f", Path: {os.path.basename(data['image_path'])}"
                elif obj_type=="pixel": details=f"Coords: {data.get('coords')}, RGB: {data.get('rgb')}"
                self.objects_text.insert(tk.END,f"- {name} ({obj_type.capitalize()}): {details}\n")
        self.objects_text.config(state=tk.DISABLED)
    def refresh_content(self): self.update_objects_display()


class StepCreatorFrame(BaseFrame):
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

        tk.Label(self, text="Step Creator", font=("Arial", 16, "bold"), bg=self["bg"]).pack(pady=5)

        toolbar_frame = tk.Frame(self, bg=self["bg"])
        toolbar_frame.pack(fill="x", padx=10, pady=(0,5))
        tk.Button(toolbar_frame, text="+ Add Step", command=self.add_step_row).pack(side=tk.LEFT, padx=2)
        tk.Button(toolbar_frame, text="Save Sequence", command=self.controller.save_sequence).pack(side=tk.LEFT, padx=2)

        header_frame = tk.Frame(self, bg=self["bg"])
        header_frame.pack(fill="x", padx=10, pady=(0,2))
        tk.Label(header_frame, text="Ord", width=4, bg=self["bg"]).pack(side=tk.LEFT, padx=(0,2))
        tk.Label(header_frame, text="Step#", width=5, bg=self["bg"]).pack(side=tk.LEFT, padx=2)
        tk.Label(header_frame, text="Object", width=17, bg=self["bg"]).pack(side=tk.LEFT, padx=2)
        tk.Label(header_frame, text="Action", width=17, bg=self["bg"]).pack(side=tk.LEFT, padx=2)
        tk.Label(header_frame, text="Parameters", bg=self["bg"]).pack(side=tk.LEFT, padx=2, fill="x", expand=True)

        self.canvas_steps = tk.Canvas(self, borderwidth=0, background="#ffffff")
        self.steps_area_frame = tk.Frame(self.canvas_steps, background="#ffffff")
        self.scrollbar_steps = tk.Scrollbar(self, orient="vertical", command=self.canvas_steps.yview)
        self.canvas_steps.configure(yscrollcommand=self.scrollbar_steps.set)
        self.scrollbar_steps.pack(side="right", fill="y", padx=(0,5), pady=5)
        self.canvas_steps.pack(side="left", fill="both", expand=True, padx=(5,0), pady=5)
        self.canvas_steps_window = self.canvas_steps.create_window((0,0), window=self.steps_area_frame, anchor="nw", tags="self.steps_area_frame")
        self.steps_area_frame.bind("<Configure>", lambda e: self.canvas_steps.configure(scrollregion=self.canvas_steps.bbox("all")))
        
        self.canvas_steps.bind("<MouseWheel>", self._on_mousewheel)
        self.steps_area_frame.bind("<MouseWheel>", self._on_mousewheel)

        self.add_step_row()

        tk.Button(self, text="Back to Main Menu", command=lambda: controller.show_frame("MainFrame")).pack(pady=10, side=tk.BOTTOM)

    def _on_mousewheel(self, event):
        self.canvas_steps.yview_scroll(int(-1*(event.delta/120)), "units")

    def add_step_row(self, step_data=None, insert_at_index=None):
        row_frame = tk.Frame(self.steps_area_frame, bg="#F0F0F0", pady=2, relief=tk.RIDGE, borderwidth=1)
        row_frame.pack(fill="x", expand=True, pady=1)

        order_btn_frame = tk.Frame(row_frame, bg=row_frame["bg"])
        order_btn_frame.pack(side=tk.LEFT, padx=(2,0), fill="y")
        tk.Button(order_btn_frame, text="▲", width=1, command=lambda idx=len(self.step_widgets): self.move_step_up(idx)).pack(pady=0, ipady=0)
        tk.Button(order_btn_frame, text="▼", width=1, command=lambda idx=len(self.step_widgets): self.move_step_down(idx)).pack(pady=0, ipady=0)

        step_num_label = tk.Label(row_frame, text="", width=4, bg=row_frame["bg"])
        step_num_label.pack(side=tk.LEFT, padx=2)

        obj_var = tk.StringVar(); action_var = tk.StringVar()
        obj_dropdown = ttk.Combobox(row_frame, textvariable=obj_var, values=self.controller.get_object_names() + ["(Global/Control)"], width=15, state="readonly")
        obj_dropdown.pack(side=tk.LEFT, padx=3)
        action_dropdown = ttk.Combobox(row_frame, textvariable=action_var, width=15, state="readonly")
        action_dropdown.pack(side=tk.LEFT, padx=3)

        params_display_frame = tk.Frame(row_frame, bg=row_frame["bg"])
        params_display_frame.pack(side=tk.LEFT, padx=3, fill="x", expand=True)
        params_edit_button = tk.Button(row_frame, text="Edit Params", width=10)
        params_edit_button.pack(side=tk.LEFT, padx=3)
        del_button = tk.Button(row_frame, text="X", fg="red", width=2, command=lambda rf=row_frame: self.delete_step_row_by_frame(rf))
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
            obj_val = step_data.get("object_name")
            obj_var.set(obj_val if obj_val else "(Global/Control)")
            action_var.set(step_data.get("action", ""))
            current_step_entry["params"] = step_data.get("params", {}).copy()
        else:
            obj_var.set("(Global/Control)")
            if insert_at_index is None:
                 self.controller.mark_sequence_modified()

        self._renumber_and_reorder_visuals()

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
            entry["step_num_label"].config(text=f"{i+1}.")
            up_button, down_button = entry["order_buttons"].winfo_children()
            up_button.config(command=lambda current_idx=i: self.move_step_up(current_idx))
            down_button.config(command=lambda current_idx=i: self.move_step_down(current_idx))
            
            entry["frame"].pack_forget()
            entry["frame"].pack(fill="x", expand=True, pady=1)

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
        selected_obj_name = obj_var.get()
        
        current_actions = []
        if selected_obj_name == "(Global/Control)":
            current_actions.extend(self.ACTION_CONFIG["_global_"]); current_actions.extend(self.ACTION_CONFIG["_control_"])
        else:
            obj_data = self.controller.objects.get(selected_obj_name)
            if obj_data:
                obj_type = obj_data.get("type")
                obj_specific_actions = self.ACTION_CONFIG.get(obj_type, [])
                current_actions = obj_specific_actions + [ga for ga in self.ACTION_CONFIG["_global_"] if ga not in obj_specific_actions]
        
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
            tk.Label(parent, text=label_text, bg=parent["bg"]).pack(side=tk.LEFT, padx=(0,1))
            var = tk.StringVar(value=str(params.get(param_key, default_value)))
            entry = tk.Entry(parent, textvariable=var, width=width)
            entry.pack(side=tk.LEFT, padx=(0,3)); step_entry["dynamic_param_widgets"][param_key] = var
            return var

        def create_labeled_combobox(parent, label_text, param_key, values_list, default_value="", width=10):
            tk.Label(parent, text=label_text, bg=parent["bg"]).pack(side=tk.LEFT, padx=(0,1))
            var = tk.StringVar(value=str(params.get(param_key, default_value)))
            if default_value not in values_list and values_list: var.set(values_list[0])
            elif not values_list: var.set("")
            combo = ttk.Combobox(parent, textvariable=var, values=values_list, width=width, state="readonly")
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
            if params: tk.Label(frame,text=f"Btn:{params.get('button','L')}, Clicks:{params.get('clicks',1)}", bg=frame["bg"], font=("Arial",7)).pack(side=tk.LEFT)
        elif action == "Scroll":
            step_entry["params_button"].pack(side=tk.LEFT, padx=3)
            if params: tk.Label(frame,text=f"Dir:{params.get('direction','Down')}, Amt:{params.get('amount',10)}", bg=frame["bg"], font=("Arial",7)).pack(side=tk.LEFT)
        elif action == "Wait for Image":
            create_labeled_entry(frame, "Timeout:", "timeout_s", 10, width=4)
            create_labeled_entry(frame, "Conf:", "confidence", params.get("confidence", self.controller.objects.get(step_entry["obj_var"].get(), {}).get("confidence",0.8)), width=4)
        elif action == "Wait for Pixel Color":
            create_labeled_entry(frame, "Timeout:", "timeout_s", 10, width=4); step_entry["params_button"].pack(side=tk.LEFT, padx=3)
        elif action == "Goto Step":
            create_labeled_entry(frame, "Target Step#:", "target_step", 1, width=4)
        elif action == "If Image Found":
            tk.Label(frame, text="If Obj:", bg=frame["bg"]).pack(side=tk.LEFT, padx=(0,1))
            cond_obj_var = tk.StringVar(value=params.get("condition_object_name", ""))
            cond_obj_combo = ttk.Combobox(frame, textvariable=cond_obj_var, values=self.controller.get_object_names(object_type="image"), width=10, state="readonly")
            cond_obj_combo.pack(side=tk.LEFT, padx=(0,2)); step_entry["dynamic_param_widgets"]["condition_object_name"] = cond_obj_var
            create_labeled_entry(frame, "Then#:", "then_step", params.get("then_step",1), width=3)
            create_labeled_entry(frame, "Else#:", "else_step", params.get("else_step","Next"), width=4)
            create_labeled_entry(frame, "Conf:", "confidence", params.get("confidence",0.8), width=3)
        elif action == "If Pixel Color":
            tk.Label(frame, text="If Obj:", bg=frame["bg"]).pack(side=tk.LEFT, padx=(0,1))
            cond_obj_var = tk.StringVar(value=params.get("condition_object_name", ""))
            cond_obj_combo = ttk.Combobox(frame, textvariable=cond_obj_var, values=self.controller.get_object_names(object_type="pixel"), width=10, state="readonly")
            cond_obj_combo.pack(side=tk.LEFT, padx=(0,2)); step_entry["dynamic_param_widgets"]["condition_object_name"] = cond_obj_var
            create_labeled_entry(frame, "Then#:", "then_step", params.get("then_step",1), width=3)
            create_labeled_entry(frame, "Else#:", "else_step", params.get("else_step","Next"), width=4)
            step_entry["params_button"].pack(side=tk.LEFT, padx=3)

    def edit_step_params_dialog(self, step_entry):
        action = step_entry["action_var"].get(); obj_name = step_entry["obj_var"].get()
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
        all_obj_names = self.controller.get_object_names() + ["(Global/Control)"]
        for step_entry in self.step_widgets:
            current_selection = step_entry["obj_var"].get()
            step_entry["obj_dropdown"]["values"] = all_obj_names
            if current_selection not in all_obj_names: step_entry["obj_var"].set("(Global/Control)")
            else: self.update_action_dropdown_and_params_ui(step_entry)

    def finalize_steps_for_controller(self):
        self.controller.current_steps = []
        for _, sw_entry in enumerate(self.step_widgets):
            obj_name = sw_entry["obj_var"].get(); action = sw_entry["action_var"].get()
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
                self.controller.current_steps.append({
                    "object_name": obj_name if obj_name != "(Global/Control)" else None,
                    "action": action,
                    "params": final_params
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
        tk.Label(self, text="Instructions", font=("Arial", 16, "bold"), bg=self["bg"]).pack(pady=10)
        instructions_text = """
Welcome to the Python Desktop Automation Tool!

**1. Core Concepts:**
   - **Objects**: References to screen elements (Regions, Images, Pixels). Created in "Object Creation".
   - **Steps**: Actions performed on Objects or globally. Defined in "Step Creator".
   - **Sequence**: An ordered list of steps, optionally looped.

**2. Main Menu:**
   - **New Sequence**: Clears current work and starts fresh. Prompts to save if unsaved changes.
   - **Instructions**: Shows this help.
   - **Object Creation**: Go here to define screen elements your steps will interact with.
   - **Step Creator**: Go here to build your automation sequence.
   - **File Operations**:
     - **Load Sequence**: Loads a previously saved sequence (.json file and associated images).
     - **Save Sequence As...**: Saves the current sequence to a new project folder.
   - **Loops**: Set how many times the entire sequence should run (0 for infinite).
   - **Run Sequence**: Executes the currently defined steps.

**3. Object Creation Menu:**
   - Name all objects uniquely.
   - **Region Creation**:
     - Grid Mode: Define X by Y grid, click cells, confirm, name it.
     - Drag Mode: Click-drag a rectangle on screen, name it.
     - Pixel Monitor: Click "Pixel Monitor", then "Capture Pixel...", move mouse to target, click. Name it.
   - **Image Creation**:
     - Grid/Drag Mode (Capture): Similar to region, but captures as an image file. Images are saved within the project folder when the sequence is saved.
   - **Created Objects List**: Shows currently defined objects.

**4. Step Creator Menu:**
   - **Header**: Shows "Ord" (Order), "Step#", "Object", "Action", "Parameters".
   - **Adding Steps**: Click "+ Add Step" from the toolbar.
   - **Ordering Steps**: Use the "▲" and "▼" buttons to move steps up or down.
   - **Configuring a Step**:
     - **Object**: Select a pre-defined object, or "(Global/Control)" for actions not tied to a specific screen element (like Wait, Keyboard, or Logic steps).
     - **Action**: Select an action. Available actions depend on the selected Object type.
     - **Parameters**: Simple parameters (e.g., Wait duration, Goto target) appear directly. For complex actions (e.g., Click types, Scroll options, RGB values), an "Edit Params" button will appear.
     - **Keyboard Actions**:
       - **Keyboard Input**: For typing a string of text.
       - **Press Key**: For pressing a single special key (e.g., Enter, F1). Select from the dropdown.
       - **Hotkey Combo**: For common multi-key combinations (e.g., Ctrl+C). Select from the dropdown.
   - **Logic Actions**:
     - **Goto Step**: Unconditionally jumps to the specified Step Number.
     - **If Image Found**: Checks for an Image Object. Jumps to "Then Step#" if found, or "Else Step#" if not.
     - **If Pixel Color**: Checks a Pixel Object's color. Jumps to "Then Step#" if it matches, or "Else Step#" if not.
   - **Deleting Steps**: Click the "X" button on a step row.
   - **Save Sequence**: Saves the current steps and objects to the loaded project file.

**5. Running & Saving:**
   - Failsafe: Move mouse to top-left screen corner to abort. Ctrl+C in terminal also stops.
   - An asterisk (*) in the window title indicates unsaved changes.

**Tips:**
   - Save frequently!
   - Test parts of your sequence often.
   - Use descriptive names for objects and sequences.
"""
        text_area = scrolledtext.ScrolledText(self, wrap=tk.WORD, height=20, width=70, font=("Arial", 9))
        text_area.insert(tk.INSERT, instructions_text)
        text_area.config(state=tk.DISABLED, bg="#F0F0F0", relief=tk.FLAT, borderwidth=0)
        text_area.pack(pady=10, padx=10, fill="both", expand=True)
        tk.Button(self, text="Back to Main Menu", command=lambda: controller.show_frame("MainFrame")).pack(pady=10)


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
    app_root = tk.Tk()
    try:
        style = ttk.Style(app_root)
        if 'clam' in style.theme_names(): style.theme_use('clam')
        elif 'vista' in style.theme_names(): style.theme_use('vista')
    except tk.TclError: print("TTK themes not available or failed to apply.")
    app_instance = DesktopAutomationApp(app_root)
    if hasattr(app_instance.frames["StepCreatorFrame"], 'finalize_steps_for_controller'):
        app_instance.frames["StepCreatorFrame"].finalize_steps_for_controller()
    app_root.mainloop()