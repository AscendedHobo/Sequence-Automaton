Automation Maker 2

Standalone project for the desktop sequence builder originally from the Useful-tools monorepo.

Features
- Create reusable Objects: regions, images, pointRGB
- Build step sequences: Click, Wait, Scroll, Keyboard Input, Hotkey Combo
- Control flow: If Image Found, If Pixel Color, Goto Step
- Save/load sequences, loop execution
- Experimental node-graph model for future visual editor

Quick Start
- Requirements: Python 3.10+ on Windows
- Install: pip install -r requirements.txt
- Run: python -m automation_maker2

Project Layout
- src/automation_maker2/app.py: main application code (copied from original)
- src/automation_maker2/__main__.py: entrypoint to launch the app
- src/automation_maker2/graph_model.py: in-memory workflow graph representation
- src/automation_maker2/graph_view.py: Tkinter Canvas view for graphs
- src/automation_maker2/graph_controller.py: glue layer between model and view
- requirements.txt: runtime dependencies

Notes
- The app uses Tkinter for UI, PyAutoGUI for input automation, and Pillow for image operations.
- When scanning/clicking, moving the mouse to the top-left corner quickly triggers PyAutoGUI failsafe.
