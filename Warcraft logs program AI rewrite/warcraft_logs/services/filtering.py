"""Filtering state management for the raid analysis UI."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Sequence


@dataclass(slots=True)
class FilterState:
    """Stores all UI selectable filters."""

    encounter_ids: Sequence[int] = field(default_factory=tuple)
    selected_encounter: int | None = None
    death_threshold: int | None = None
    time_range: tuple[float, float] | None = None
    unit_ids: Sequence[str] = field(default_factory=tuple)
    selected_units: Sequence[str] = field(default_factory=tuple)
    spell_ids: Sequence[int] = field(default_factory=tuple)
    selected_spells: Sequence[int] = field(default_factory=tuple)
    event_types: Sequence[str] = field(default_factory=tuple)
    selected_event_types: Sequence[str] = field(default_factory=tuple)

    def with_encounter(self, encounter_id: int | None) -> "FilterState":
        return FilterState(
            encounter_ids=self.encounter_ids,
            selected_encounter=encounter_id,
            death_threshold=self.death_threshold,
            time_range=self.time_range,
            unit_ids=self.unit_ids,
            selected_units=self.selected_units,
            spell_ids=self.spell_ids,
            selected_spells=self.selected_spells,
            event_types=self.event_types,
            selected_event_types=self.selected_event_types,
        )

    def matches_event(self, event: dict[str, object]) -> bool:
        if self.selected_encounter is not None and event.get("encounter_id") != self.selected_encounter:
            return False
        if self.time_range is not None:
            start, end = self.time_range
            relative_time = float(event.get("relative_time", 0.0))
            if relative_time < start or relative_time > end:
                return False
        if self.selected_units and event.get("source_id") not in self.selected_units:
            return False
        if self.selected_spells and event.get("spell_id") not in self.selected_spells:
            return False
        if self.selected_event_types and event.get("event_name") not in self.selected_event_types:
            return False
        return True

    @staticmethod
    def from_log(log_frame) -> "FilterState":  # type: ignore[override]
        encounter_ids = tuple(
            sorted(int(value) for value in log_frame["encounter_id"].dropna().unique())
        )
        unit_ids = tuple(sorted(str(value) for value in log_frame["source_id"].dropna().unique()))
        raw_spell_ids = log_frame["spell_id"].dropna().unique()
        spell_ids = tuple(
            sorted(
                {
                    int(spell_id)
                    for spell_id in raw_spell_ids
                    if isinstance(spell_id, (int, float))
                }
            )
        )
        event_types = tuple(sorted(log_frame["event_name"].dropna().unique()))
        return FilterState(
            encounter_ids=encounter_ids,
            unit_ids=unit_ids,
            spell_ids=spell_ids,
            event_types=event_types,
        )

    def update_selection(
        self,
        *,
        encounter: int | None = None,
        units: Iterable[str] | None = None,
        spells: Iterable[int] | None = None,
        event_types: Iterable[str] | None = None,
        death_threshold: int | None = None,
        time_range: tuple[float, float] | None = None,
    ) -> "FilterState":
        return FilterState(
            encounter_ids=self.encounter_ids,
            selected_encounter=encounter if encounter is not None else self.selected_encounter,
            death_threshold=death_threshold if death_threshold is not None else self.death_threshold,
            time_range=time_range if time_range is not None else self.time_range,
            unit_ids=self.unit_ids,
            selected_units=tuple(units) if units is not None else self.selected_units,
            spell_ids=self.spell_ids,
            selected_spells=tuple(spells) if spells is not None else self.selected_spells,
            event_types=self.event_types,
            selected_event_types=tuple(event_types) if event_types is not None else self.selected_event_types,
        )


__all__ = ["FilterState"]
