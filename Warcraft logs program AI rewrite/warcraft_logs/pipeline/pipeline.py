"""High level orchestration of the combat log processing pipeline."""
from __future__ import annotations

from dataclasses import dataclass
import logging
from pathlib import Path
from typing import Iterable

import pandas as pd

from ..config import AppConfig
from ..data_models import CombatLogEvent, NormalisedCombatLog
from .log_loader import CombatLogLoader
from .normalizer import CombatLogNormaliser, NormaliserResult

LOGGER = logging.getLogger(__name__)


@dataclass(slots=True)
class PipelineOutput:
    """Container for all intermediate artefacts produced by the pipeline."""

    raw_events: list[CombatLogEvent]
    normalised_log: NormalisedCombatLog
    csv_path: Path
    raw_csv_path: Path


class CombatLogPipeline:
    """Complete end-to-end combat log processing pipeline."""

    def __init__(self, config: AppConfig) -> None:
        self._config = config
        self._loader = CombatLogLoader()
        self._normaliser = CombatLogNormaliser(config)

    def run(self, input_path: Path) -> PipelineOutput:
        LOGGER.info("Running pipeline for %s", input_path)
        events = self._loader.load(input_path)
        raw_csv_path = self._persist_raw_events(events)
        normalised = self._normaliser.normalise(events)
        return PipelineOutput(
            raw_events=events,
            normalised_log=normalised.normalised_log,
            csv_path=normalised.output_path,
            raw_csv_path=raw_csv_path,
        )

    def run_on_events(self, events: Iterable[CombatLogEvent]) -> NormaliserResult:
        return self._normaliser.normalise(list(events))

    def _persist_raw_events(self, events: Iterable[CombatLogEvent]) -> Path:
        output_dir = self._config.log_output_directory
        output_dir.mkdir(parents=True, exist_ok=True)
        raw_path = output_dir / "combat_log_with_floats.csv"
        records = [event.to_record() for event in events]
        if records:
            pd.DataFrame.from_records(records).to_csv(raw_path, index=False)
        else:
            raw_path.touch()
        return raw_path


__all__ = ["CombatLogPipeline", "PipelineOutput"]
