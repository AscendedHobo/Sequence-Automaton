"""State containers for the Tkinter UI."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from ..data_models import NormalisedCombatLog
from ..services.filtering import FilterState
from ..services.movement import MovementSummary


@dataclass(slots=True)
class AppState:
    """Mutable state shared between controller and view."""

    log_path: Optional[Path] = None
    normalised_log: Optional[NormalisedCombatLog] = None
    filter_state: FilterState = field(default_factory=FilterState)
    movement_summaries: list[MovementSummary] = field(default_factory=list)


__all__ = ["AppState"]
