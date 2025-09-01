import tkinter as tk
from tkinter import ttk

from .app import DesktopAutomationApp  # type: ignore


def main() -> None:
    root = tk.Tk()
    # Apply a reasonable ttk theme if present
    try:
        style = ttk.Style(root)
        names = style.theme_names()
        if 'clam' in names:
            style.theme_use('clam')
        elif 'vista' in names:
            style.theme_use('vista')
    except tk.TclError:
        pass

    app = DesktopAutomationApp(root)
    # Ensure steps are finalized if the frame provides that API
    if hasattr(app.frames.get("StepCreatorFrame"), 'finalize_steps_for_controller'):
        try:
            app.frames["StepCreatorFrame"].finalize_steps_for_controller()
        except Exception:
            pass
    root.mainloop()


if __name__ == '__main__':
    main()

