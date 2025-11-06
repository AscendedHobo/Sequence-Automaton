from pathlib import Path

from warcraft_logs.config import load_config, AppConfig


def test_load_config(tmp_path: Path) -> None:
    config_file = tmp_path / "config.toml"
    config_file.write_text(
        """
        [paths]
        log_output_dir = "./logs"
        map_directory = "./maps"

        [processing]
        interpolation_interval = 1.0
        max_death_threshold = 3

        [visualization]
        default_plot = "scatter"
        colormap = "viridis"
        hexbin_grid_size = 30
        kde_bandwidth = 1.5

        [ui]
        window_title = "Test"
        recent_files_limit = 5
        """,
        encoding="utf-8",
    )

    config = load_config(config_file)
    assert isinstance(config, AppConfig)
    assert config.processing.interpolation_interval == 1.0
    assert config.ui.window_title == "Test"
