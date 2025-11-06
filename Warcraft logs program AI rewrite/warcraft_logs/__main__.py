"""Entrypoint for launching the WoW raid analysis application."""
from __future__ import annotations

from pathlib import Path

from .config import AppConfig, ConfigurationError, load_config
from .ui.controller import RaidAnalysisController
from .ui.state import AppState
from .ui.views.main_view import RaidAnalysisApp


def main() -> None:
    config_path = Path(__file__).resolve().parent.parent / "config.toml"
    try:
        config: AppConfig = load_config(config_path)
    except ConfigurationError as exc:  # pragma: no cover - configuration errors handled at runtime
        raise SystemExit(str(exc)) from exc

    controller = RaidAnalysisController(config, AppState())
    app = RaidAnalysisApp(controller, config)
    app.mainloop()


if __name__ == "__main__":  # pragma: no cover - script entrypoint
    main()
