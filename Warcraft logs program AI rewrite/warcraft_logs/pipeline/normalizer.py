"""Normalisation of combat log event data."""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
import logging
from pathlib import Path
from typing import Iterable, List

import numpy as np
import pandas as pd

from ..config import AppConfig
from ..data_models import CombatLogEvent, NormalisedCombatLog

LOGGER = logging.getLogger(__name__)


@dataclass(slots=True)
class NormaliserResult:
    """Encapsulates the output artefacts from normalisation."""

    normalised_log: NormalisedCombatLog
    output_path: Path


class CombatLogNormaliser:
    """Convert a list of :class:`CombatLogEvent` objects into analytics friendly data."""

    def __init__(self, config: AppConfig) -> None:
        self._config = config

    def normalise(self, events: Iterable[CombatLogEvent], *, output_path: Path | None = None) -> NormaliserResult:
        dataframe = self._to_dataframe(list(events))
        LOGGER.info("Normalised dataframe contains %s rows", len(dataframe))

        output_dir = self._config.log_output_directory
        output_dir.mkdir(parents=True, exist_ok=True)
        destination = output_path or output_dir / "filtered_combat_log.csv"
        dataframe.to_csv(destination, index=False)
        LOGGER.info("Persisted normalised combat log to %s", destination)

        return NormaliserResult(
            normalised_log=NormalisedCombatLog(events=dataframe),
            output_path=destination,
        )

    def _to_dataframe(self, events: List[CombatLogEvent]) -> pd.DataFrame:
        records = [event.to_record() for event in events]
        frame = pd.DataFrame.from_records(records)
        frame.sort_values("timestamp", inplace=True)

        frame["encounter_id"] = self._assign_encounters(frame["event_name"].to_numpy())
        frame["relative_time"] = self._compute_relative_time(frame["timestamp"].to_numpy(), frame["encounter_id"].to_numpy())
        frame["x"], frame["y"], frame["z"] = self._forward_fill_coordinates(frame)
        frame["death_count"] = self._death_counter(frame)
        return frame

    @staticmethod
    def _assign_encounters(event_names: np.ndarray) -> np.ndarray:
        encounter_id = 0
        encounter_ids = np.zeros_like(event_names, dtype=int)
        for index, event in enumerate(event_names):
            if event == "ENCOUNTER_START":
                encounter_id += 1
            encounter_ids[index] = encounter_id
        return encounter_ids

    @staticmethod
    def _compute_relative_time(timestamps: np.ndarray, encounters: np.ndarray) -> np.ndarray:
        base_times: dict[int, datetime] = {}
        relative = np.zeros_like(encounters, dtype=float)
        for index, (timestamp, encounter) in enumerate(zip(timestamps, encounters, strict=False)):
            if encounter not in base_times:
                base_times[encounter] = timestamp
            base = base_times[encounter]
            delta = timestamp - base
            relative[index] = delta.total_seconds()
        return relative

    @staticmethod
    def _forward_fill_coordinates(frame: pd.DataFrame) -> tuple[pd.Series, pd.Series, pd.Series]:
        coord_columns = ["x", "y", "z"]
        filled = frame.groupby(["encounter_id", "source_id"], dropna=False)[coord_columns].ffill()
        return filled["x"], filled["y"], filled["z"]

    @staticmethod
    def _death_counter(frame: pd.DataFrame) -> pd.Series:
        death_flag = (frame["event_name"] == "UNIT_DIED").astype(int)
        return death_flag.groupby(frame["encounter_id"]).cumsum()


__all__ = ["CombatLogNormaliser", "NormaliserResult"]
