"""Centralised logging configuration."""
from __future__ import annotations

import logging
from logging.handlers import RotatingFileHandler
from pathlib import Path

from .config import AppConfig


def configure_logging(config: AppConfig) -> None:
    """Set up root logging handlers."""

    log_dir = config.log_output_directory
    log_dir.mkdir(parents=True, exist_ok=True)

    log_path = log_dir / "raid_analysis.log"

    formatter = logging.Formatter("%(asctime)s [%(levelname)s] %(name)s: %(message)s")

    rotating_handler = RotatingFileHandler(log_path, maxBytes=5_000_000, backupCount=3)
    rotating_handler.setFormatter(formatter)

    stream_handler = logging.StreamHandler()
    stream_handler.setFormatter(formatter)

    root_logger = logging.getLogger()
    root_logger.setLevel(logging.INFO)
    root_logger.addHandler(rotating_handler)
    root_logger.addHandler(stream_handler)


__all__ = ["configure_logging"]
