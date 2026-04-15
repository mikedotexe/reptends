from pathlib import Path

from bridge_reptends import load_lean_module_index
from bridge_reptends.registry import (
    render_geometric_stack_import_lines,
    render_geometric_stack_module_lines,
    render_proof_system_legend_lines,
)


ROOT = Path(__file__).resolve().parent.parent
GEOMETRIC_STACK_SURFACE = ROOT / "lean" / "GeometricStack.lean"


def _umbrella_imports() -> list[str]:
    return [
        line.removeprefix("import ").strip()
        for line in GEOMETRIC_STACK_SURFACE.read_text().splitlines()
        if line.startswith("import GeometricStack.")
    ]


def _marked_block(text: str, start_marker: str, end_marker: str) -> str:
    return text.split(start_marker, 1)[1].split(end_marker, 1)[0].strip()


def test_geometric_stack_umbrella_imports_follow_indexed_surface() -> None:
    expected = [
        module.id
        for module in load_lean_module_index()
        if module.path.startswith("lean/GeometricStack/") and module.path.endswith(".lean")
    ]

    assert _umbrella_imports() == expected


def test_geometric_stack_import_block_is_registry_backed() -> None:
    text = GEOMETRIC_STACK_SURFACE.read_text()

    assert _marked_block(
        text,
        "-- GEOMETRIC_STACK_IMPORTS_START",
        "-- GEOMETRIC_STACK_IMPORTS_END",
    ) == "\n".join(render_geometric_stack_import_lines())


def test_geometric_stack_module_summary_block_is_registry_backed() -> None:
    text = GEOMETRIC_STACK_SURFACE.read_text()

    assert _marked_block(
        text,
        "<!-- GEOMETRIC_STACK_MODULES_START -->",
        "<!-- GEOMETRIC_STACK_MODULES_END -->",
    ) == "\n".join(render_geometric_stack_module_lines())


def test_geometric_stack_uses_shared_proof_system_legend() -> None:
    text = GEOMETRIC_STACK_SURFACE.read_text()

    assert _marked_block(
        text,
        "<!-- PROOF_SYSTEM_LEGEND_START -->",
        "<!-- PROOF_SYSTEM_LEGEND_END -->",
    ) == "\n".join(render_proof_system_legend_lines())
