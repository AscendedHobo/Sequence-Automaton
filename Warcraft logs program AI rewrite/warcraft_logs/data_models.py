"""Data models for World of Warcraft combat logs."""
from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, Mapping, MutableMapping, Optional

from pandas import DataFrame


@dataclass(slots=True)
class CombatLogEvent:
    """Represents a single event extracted from a combat log."""

    timestamp: datetime
    event_name: str
    source_id: str
    source_name: str
    dest_id: str
    dest_name: str
    spell_id: Optional[int]
    spell_name: Optional[str]
    amount: Optional[float]
    x: Optional[float]
    y: Optional[float]
    z: Optional[float]
    extras: MutableMapping[str, Any] = field(default_factory=dict)

    def to_record(self) -> Mapping[str, Any]:
        """Return a mapping suitable for DataFrame construction."""

        return {
            "timestamp": self.timestamp,
            "event_name": self.event_name,
            "source_id": self.source_id,
            "source_name": self.source_name,
            "dest_id": self.dest_id,
            "dest_name": self.dest_name,
            "spell_id": self.spell_id,
            "spell_name": self.spell_name,
            "amount": self.amount,
            "x": self.x,
            "y": self.y,
            "z": self.z,
            **self.extras,
        }


@dataclass(slots=True)
class NormalisedCombatLog:
    """Container for the normalised combat log data set."""

    events: DataFrame

    def filter_by_encounter(self, encounter_id: int) -> "NormalisedCombatLog":
        """Return a view of the events belonging to a single encounter."""

        mask = self.events["encounter_id"] == encounter_id
        return NormalisedCombatLog(events=self.events.loc[mask].copy())


__all__ = [
    "CombatLogEvent",
    "NormalisedCombatLog",
]
