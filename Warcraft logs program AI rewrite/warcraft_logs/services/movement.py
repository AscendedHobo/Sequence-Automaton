"""Movement analysis utilities."""
from __future__ import annotations

from dataclasses import dataclass
import logging
from typing import Iterable

import numpy as np
import pandas as pd

from ..data_models import NormalisedCombatLog

LOGGER = logging.getLogger(__name__)


@dataclass(slots=True)
class MovementSummary:
    """Holds aggregate movement statistics for a single unit."""

    unit_id: str
    unit_name: str
    mean_path: pd.DataFrame
    displacement: float
    path_variance: float


class MovementAnalyser:
    """Compute movement metrics from a :class:`NormalisedCombatLog`."""

    def __init__(self, interval: float) -> None:
        self._interval = interval

    def summarise(self, log: NormalisedCombatLog, *, unit_ids: Iterable[str] | None = None) -> list[MovementSummary]:
        events = log.events
        if unit_ids is not None:
            events = events[events["source_id"].isin(list(unit_ids))]
        if events.empty:
            return []

        summaries: list[MovementSummary] = []
        for unit_id, group in events.groupby("source_id"):
            unit_name = group["source_name"].iloc[0] if not group["source_name"].isna().all() else unit_id
            resampled = self._resample_unit(group)
            displacement = self._compute_displacement(resampled)
            variance = self._path_variance(resampled)
            summaries.append(
                MovementSummary(
                    unit_id=unit_id,
                    unit_name=unit_name,
                    mean_path=resampled,
                    displacement=displacement,
                    path_variance=variance,
                )
            )
        return summaries

    def _resample_unit(self, frame: pd.DataFrame) -> pd.DataFrame:
        frame = frame.sort_values("relative_time")
        frame = frame.drop_duplicates(subset="relative_time", keep="last")
        time_index = np.arange(frame["relative_time"].min(), frame["relative_time"].max() + self._interval, self._interval)
        resampled = frame.set_index("relative_time").reindex(time_index).interpolate(method="linear")
        resampled.index.name = "relative_time"
        return resampled.reset_index()

    @staticmethod
    def _compute_displacement(frame: pd.DataFrame) -> float:
        if frame[["x", "y"]].isna().any().any():
            frame = frame.dropna(subset=["x", "y"], how="any")
        if frame.empty:
            return 0.0
        start = frame.iloc[0][["x", "y"]].to_numpy(dtype=float)
        end = frame.iloc[-1][["x", "y"]].to_numpy(dtype=float)
        return float(np.linalg.norm(end - start))

    @staticmethod
    def _path_variance(frame: pd.DataFrame) -> float:
        if frame[["x", "y"]].isna().any().any():
            frame = frame.dropna(subset=["x", "y"], how="any")
        if frame.empty:
            return 0.0
        centroid = frame[["x", "y"]].mean().to_numpy(dtype=float)
        deltas = frame[["x", "y"]].to_numpy(dtype=float) - centroid
        return float(np.mean(np.sum(deltas**2, axis=1)))


__all__ = ["MovementAnalyser", "MovementSummary"]
