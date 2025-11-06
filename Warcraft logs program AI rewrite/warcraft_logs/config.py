"""Application configuration loading and validation utilities."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping
import tomllib


class ConfigurationError(RuntimeError):
    """Raised when the configuration file cannot be loaded or is invalid."""


@dataclass(frozen=True, slots=True)
class PathsConfig:
    """Filesystem locations used by the application."""

    log_output_dir: Path
    map_directory: Path


@dataclass(frozen=True, slots=True)
class ProcessingConfig:
    """Controls how combat logs are processed."""

    interpolation_interval: float
    max_death_threshold: int


@dataclass(frozen=True, slots=True)
class VisualizationConfig:
    """Default options for the Matplotlib visualisations."""

    default_plot: str
    colormap: str
    hexbin_grid_size: int
    kde_bandwidth: float


@dataclass(frozen=True, slots=True)
class UIConfig:
    """UI related defaults."""

    window_title: str
    recent_files_limit: int


@dataclass(frozen=True, slots=True)
class AppConfig:
    """Top level configuration object."""

    paths: PathsConfig
    processing: ProcessingConfig
    visualization: VisualizationConfig
    ui: UIConfig

    @property
    def log_output_directory(self) -> Path:
        """Return the resolved output directory for processed logs."""

        return self.paths.log_output_dir

    @property
    def map_directory(self) -> Path:
        """Return the resolved path containing encounter maps."""

        return self.paths.map_directory


def _load_toml(path: Path) -> Mapping[str, Any]:
    try:
        with path.open("rb") as buffer:
            return tomllib.load(buffer)
    except FileNotFoundError as error:
        raise ConfigurationError(f"Configuration file not found: {path}") from error
    except tomllib.TOMLDecodeError as error:
        raise ConfigurationError(f"Invalid TOML in configuration file {path}") from error


def load_config(path: Path | None = None) -> AppConfig:
    """Load the application configuration from the supplied path."""

    config_path = path or Path(__file__).resolve().parent.parent / "config.toml"
    raw = _load_toml(config_path)

    try:
        paths = raw["paths"]
        processing = raw["processing"]
        visualization = raw["visualization"]
        ui = raw["ui"]
    except KeyError as error:
        raise ConfigurationError(f"Missing configuration section: {error.args[0]}") from error

    return AppConfig(
        paths=PathsConfig(
            log_output_dir=Path(paths["log_output_dir"]).expanduser().resolve(),
            map_directory=Path(paths["map_directory"]).expanduser().resolve(),
        ),
        processing=ProcessingConfig(
            interpolation_interval=float(processing["interpolation_interval"]),
            max_death_threshold=int(processing["max_death_threshold"]),
        ),
        visualization=VisualizationConfig(
            default_plot=str(visualization["default_plot"]),
            colormap=str(visualization["colormap"]),
            hexbin_grid_size=int(visualization["hexbin_grid_size"]),
            kde_bandwidth=float(visualization["kde_bandwidth"]),
        ),
        ui=UIConfig(
            window_title=str(ui["window_title"]),
            recent_files_limit=int(ui["recent_files_limit"]),
        ),
    )


__all__ = [
    "AppConfig",
    "ConfigurationError",
    "PathsConfig",
    "ProcessingConfig",
    "VisualizationConfig",
    "UIConfig",
    "load_config",
]
