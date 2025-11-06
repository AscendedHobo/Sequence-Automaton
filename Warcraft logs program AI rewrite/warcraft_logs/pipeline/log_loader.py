"""Utilities for loading and filtering raw combat log files."""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
import csv
import logging
import re
from pathlib import Path
from typing import Iterable, Iterator, List, Sequence

from ..data_models import CombatLogEvent

LOGGER = logging.getLogger(__name__)

TIMESTAMP_FORMAT = "%m/%d %H:%M:%S.%f"

FLOAT_PATTERN = re.compile(r"[-+]?[0-9]*\.[0-9]+")
HEADER_PATTERN = re.compile(r"^(?P<timestamp>\d+/\d+ \d+:\d+:\d+\.\d+)\s+(?P<event>[A-Z_]+),(?P<payload>.*)$")
COORDINATE_KEYS: Sequence[str] = ("X", "Y", "Z")


@dataclass(slots=True)
class LogLoaderConfig:
    """Configuration for the :class:`CombatLogLoader`."""

    keep_events: Sequence[str]


DEFAULT_EVENTS_TO_KEEP: Sequence[str] = (
    "SPELL_CAST_START",
    "SPELL_CAST_SUCCESS",
    "SPELL_DAMAGE",
    "SPELL_HEAL",
    "SWING_DAMAGE",
    "SWING_MISSED",
    "RANGE_DAMAGE",
    "SPELL_AURA_APPLIED",
    "SPELL_AURA_REMOVED",
    "SPELL_PERIODIC_DAMAGE",
    "SPELL_PERIODIC_HEAL",
    "UNIT_DIED",
    "ENCOUNTER_START",
    "ENCOUNTER_END",
    "SPELL_SUMMON",
    "SPELL_RESURRECT",
)


class CombatLogLoader:
    """Parse raw Blizzard combat logs into :class:`CombatLogEvent` objects."""

    def __init__(self, config: LogLoaderConfig | None = None) -> None:
        self._config = config or LogLoaderConfig(keep_events=DEFAULT_EVENTS_TO_KEEP)

    def load(self, path: Path) -> List[CombatLogEvent]:
        """Parse the log file located at *path*."""

        LOGGER.info("Parsing combat log at %s", path)
        events: List[CombatLogEvent] = []
        with path.open("r", encoding="utf-8", errors="ignore") as handle:
            for line_number, line in enumerate(handle, start=1):
                line = line.strip()
                if not line:
                    continue
                try:
                    event = self._parse_line(line)
                except ValueError as exc:
                    LOGGER.debug("Skipping unparsable line %s: %s", line_number, exc)
                    continue
                if event is None:
                    continue
                events.append(event)
        LOGGER.info("Parsed %s events from %s", len(events), path)
        return events

    def _parse_line(self, line: str) -> CombatLogEvent | None:
        match = HEADER_PATTERN.match(line)
        if not match:
            raise ValueError("Line missing header components")

        timestamp_str = match.group("timestamp")
        event_name = match.group("event")
        payload = match.group("payload")

        if not self._should_keep(event_name, payload):
            return None

        timestamp = datetime.strptime(timestamp_str, TIMESTAMP_FORMAT)
        fields = self._parse_payload(payload)
        return self._build_event(timestamp, event_name, fields)

    def _parse_payload(self, payload: str) -> List[str]:
        reader = csv.reader([payload])
        return next(reader)

    def _should_keep(self, event_name: str, payload: str) -> bool:
        if event_name in self._config.keep_events:
            return True
        return bool(FLOAT_PATTERN.search(payload))

    def _build_event(self, timestamp: datetime, event_name: str, fields: Sequence[str]) -> CombatLogEvent:
        field_iter = iter(fields)
        source_guid = next(field_iter, "")
        source_name = next(field_iter, "")
        dest_guid = next(field_iter, "")
        dest_name = next(field_iter, "")

        spell_id = self._pop_optional_int(field_iter)
        spell_name = self._pop_optional_str(field_iter)

        amount = self._pop_optional_float(field_iter)
        coordinates = self._extract_coordinates(field_iter)

        extras = {f"extra_{index}": value for index, value in enumerate(field_iter)}

        return CombatLogEvent(
            timestamp=timestamp,
            event_name=event_name,
            source_id=source_guid,
            source_name=source_name.strip('"'),
            dest_id=dest_guid,
            dest_name=dest_name.strip('"'),
            spell_id=spell_id,
            spell_name=spell_name,
            amount=amount,
            x=coordinates.get("X"),
            y=coordinates.get("Y"),
            z=coordinates.get("Z"),
            extras=extras,
        )

    @staticmethod
    def _pop_optional_int(fields: Iterator[str]) -> int | None:
        value = next(fields, "")
        try:
            return int(value)
        except (TypeError, ValueError):
            return None

    @staticmethod
    def _pop_optional_str(fields: Iterator[str]) -> str | None:
        value = next(fields, "")
        value = value.strip()
        return value.strip('"') or None

    @staticmethod
    def _pop_optional_float(fields: Iterator[str]) -> float | None:
        value = next(fields, "")
        try:
            return float(value)
        except (TypeError, ValueError):
            return None

    @staticmethod
    def _extract_coordinates(fields: Iterable[str]) -> dict[str, float | None]:
        coordinates: dict[str, float | None] = {key: None for key in COORDINATE_KEYS}
        for label, value in zip(COORDINATE_KEYS, fields):
            try:
                coordinates[label] = float(value)
            except (TypeError, ValueError):
                coordinates[label] = None
        return coordinates


__all__ = ["CombatLogLoader", "LogLoaderConfig", "DEFAULT_EVENTS_TO_KEEP"]
