Automation Maker 2

Standalone project for the desktop sequence builder originally from the Useful-tools monorepo.

Features
- Create reusable Objects: regions, images, pixels
- Build step sequences: Click, Wait, Scroll, Keyboard Input, Hotkey Combo
- Control flow: If Image Found, If Pixel Color, Goto Step
- Save/load sequences, loop execution

Quick Start
- Requirements: Python 3.10+ on Windows
- Install: pip install -r requirements.txt
- Run: python -m automation_maker2

Project Layout
- src/automation_maker2/app.py: main application code (copied from original)
- src/automation_maker2/__main__.py: entrypoint to launch the app
- requirements.txt: runtime dependencies

Notes
- The app uses Tkinter for UI, PyAutoGUI for input automation, and Pillow for image operations.
- When scanning/clicking, moving the mouse to the top-left corner quickly triggers PyAutoGUI failsafe.

