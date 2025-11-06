"""Controller layer bridging the UI and data processing pipeline."""
from __future__ import annotations

import logging
from pathlib import Path
from typing import Iterable

import pandas as pd

from ..config import AppConfig
from ..data_models import NormalisedCombatLog
from ..logging_utils import configure_logging
from ..pipeline.pipeline import CombatLogPipeline, PipelineOutput
from ..services.filtering import FilterState
from ..services.movement import MovementAnalyser
from .state import AppState

LOGGER = logging.getLogger(__name__)


class RaidAnalysisController:
    """Coordinates pipeline execution and exposes data to the UI layer."""

    def __init__(self, config: AppConfig, state: AppState | None = None) -> None:
        self._config = config
        configure_logging(config)
        self._pipeline = CombatLogPipeline(config)
        self._movement = MovementAnalyser(config.processing.interpolation_interval)
        self._state = state or AppState()

    @property
    def state(self) -> AppState:
        return self._state

    def load_log(self, path: Path) -> PipelineOutput:
        LOGGER.info("Loading combat log from %s", path)
        output = self._pipeline.run(path)
        self._state.log_path = path
        self._state.normalised_log = output.normalised_log
        self._state.filter_state = FilterState.from_log(output.normalised_log.events)
        self._state.movement_summaries = self._movement.summarise(output.normalised_log)
        return output

    def apply_filters(
        self,
        *,
        encounter: int | None = None,
        units: Iterable[str] | None = None,
        spells: Iterable[int] | None = None,
        event_types: Iterable[str] | None = None,
        death_threshold: int | None = None,
        time_range: tuple[float, float] | None = None,
    ) -> pd.DataFrame:
        if self._state.normalised_log is None:
            raise RuntimeError("No combat log has been loaded")

        self._state.filter_state = self._state.filter_state.update_selection(
            encounter=encounter,
            units=units,
            spells=spells,
            event_types=event_types,
            death_threshold=death_threshold,
            time_range=time_range,
        )

        filtered = self._filter_dataframe(self._state.normalised_log.events)
        LOGGER.info("Filtered dataset contains %s rows", len(filtered))
        return filtered

    def _filter_dataframe(self, frame: pd.DataFrame) -> pd.DataFrame:
        state = self._state.filter_state
        mask = frame.apply(state.matches_event, axis=1)
        if state.death_threshold is not None:
            mask &= frame["death_count"].fillna(0) <= state.death_threshold
        filtered = frame.loc[mask].copy()
        LOGGER.debug("Filter mask reduced data set to %s rows", len(filtered))
        return filtered

    def refresh_movement(self, units: Iterable[str] | None = None) -> list:
        if self._state.normalised_log is None:
            raise RuntimeError("No combat log has been loaded")
        summaries = self._movement.summarise(self._state.normalised_log, unit_ids=units)
        self._state.movement_summaries = summaries
        return summaries

    def get_available_spells(self) -> list[tuple[int, str]]:
        if self._state.normalised_log is None:
            return []
        frame = self._state.normalised_log.events
        spells = (
            frame[["spell_id", "spell_name"]]
            .dropna(subset=["spell_id"])
            .drop_duplicates()
            .assign(spell_name=lambda df: df["spell_name"].fillna(df["spell_id"].astype(str)))
            .sort_values("spell_name")
        )
        return list(spells.itertuples(index=False, name=None))

    def get_available_units(self) -> list[tuple[str, str]]:
        if self._state.normalised_log is None:
            return []
        frame = self._state.normalised_log.events
        units = (
            frame[["source_id", "source_name"]]
            .dropna(subset=["source_id"])
            .drop_duplicates()
            .assign(source_name=lambda df: df["source_name"].fillna(df["source_id"]))
            .sort_values("source_name")
        )
        return list(units.itertuples(index=False, name=None))


__all__ = ["RaidAnalysisController"]
