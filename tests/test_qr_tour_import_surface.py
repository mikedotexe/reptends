from pathlib import Path

from bridge_reptends import load_lean_module_index
from bridge_reptends.registry import render_qr_tour_import_lines


ROOT = Path(__file__).resolve().parent.parent
QRT_SURFACE = ROOT / "lean" / "QRTour.lean"


def _umbrella_imports() -> list[str]:
    return [
        line.removeprefix("import ").strip()
        for line in QRT_SURFACE.read_text().splitlines()
        if line.startswith("import QRTour.")
    ]


def _marked_block(text: str, start_marker: str, end_marker: str) -> str:
    return text.split(start_marker, 1)[1].split(end_marker, 1)[0].strip()


def test_qr_tour_umbrella_imports_follow_indexed_qr_tour_surface() -> None:
    expected = [
        module.id
        for module in load_lean_module_index()
        if module.path.startswith("lean/QRTour/") and module.path.endswith(".lean")
    ]

    assert _umbrella_imports() == expected


def test_qr_tour_umbrella_import_block_is_registry_backed() -> None:
    text = QRT_SURFACE.read_text()

    assert _marked_block(text, "-- QRT_SURFACE_IMPORTS_START", "-- QRT_SURFACE_IMPORTS_END") == "\n".join(
        render_qr_tour_import_lines()
    )
