# Warcraft Raid Analysis Rewrite

Modernised implementation of the original World of Warcraft raid combat log analysis pipeline.

## Features

- End-to-end pipeline for parsing raw Blizzard combat logs, normalising events, and preparing analytics data.
- Modular service layer for filtering, movement aggregation, and future analytics extensions.
- Tkinter-based desktop UI with drag & drop support, multiple plot types (scatter, hexbin, KDE, path visualisation), and filter controls.
- Configuration via `config.toml` with type-safe dataclasses and validation logic.
- Logging with rotating file handler and console output.
- PyProject-based packaging with entry point `warcraft-raid-analysis`.

## Getting Started

```bash
pip install -e ".[develop]"
python -m warcraft_logs
```

Place combat logs in `logs/` by default or configure directories within `config.toml`.
