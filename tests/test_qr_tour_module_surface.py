import re
from pathlib import Path

from bridge_reptends import load_claim_registry, load_lean_claim_carriers, load_lean_module_index


ROOT = Path(__file__).resolve().parent.parent
QRT_SURFACE = ROOT / "lean" / "QRTour.lean"
MODULE_ID_PATTERN = re.compile(r"^- `([^`]+)`")


def _section(text: str, start_heading: str, end_heading: str) -> str:
    return text.split(start_heading, 1)[1].split(end_heading, 1)[0]


def _bullet_ids(section: str) -> list[str]:
    return [
        match.group(1)
        for line in section.splitlines()
        if (match := MODULE_ID_PATTERN.match(line))
    ]


def _lean_module_id(module_path: str) -> str:
    return module_path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")


def _theorem_surface_claim_module_rows(section: str) -> list[tuple[str, list[str]]]:
    bullet_blocks: list[str] = []
    current: list[str] = []
    for line in section.splitlines():
        stripped = line.strip()
        if stripped.startswith("- `"):
            if current:
                bullet_blocks.append(" ".join(current))
            current = [stripped]
        elif current and stripped:
            current.append(stripped)
        elif current:
            bullet_blocks.append(" ".join(current))
            current = []
    if current:
        bullet_blocks.append(" ".join(current))

    rows: list[tuple[str, list[str]]] = []
    for block in bullet_blocks:
        ids = re.findall(r"`([^`]+)`", block)
        modules = [name for name in ids if name.startswith("QRTour.")]
        claims = [name for name in ids if not name.startswith("QRTour.")]
        rows.extend((claim_id, modules) for claim_id in claims)
    return rows


def test_qr_tour_module_section_follows_indexed_module_order() -> None:
    text = QRT_SURFACE.read_text()
    modules_section = _section(text, "## Modules", "## Notes On Agda Correspondence")

    expected = [
        module.id
        for module in load_lean_module_index()
        if module.path.startswith("lean/QRTour/") and module.path.endswith(".lean")
    ]
    listed_modules = _bullet_ids(modules_section)

    assert listed_modules == expected


def test_qr_tour_open_boundary_tracks_registry_open_claims() -> None:
    text = QRT_SURFACE.read_text()
    boundary_section = _section(text, "## Exact/Open Boundary", "## Example: p = 97, base = 10, m = 2, B = 100")

    expected_open_claims = [claim.id for claim in load_claim_registry() if claim.status == "open"]
    boundary_claims = _bullet_ids(boundary_section)

    assert boundary_claims == expected_open_claims
    for line in boundary_section.splitlines():
        if line.startswith("- `"):
            assert "remains `open`" in line


def test_qr_tour_theorem_surface_tracks_claim_carrier_order_and_modules() -> None:
    text = QRT_SURFACE.read_text()
    theorem_surface = _section(text, "## Current Theorem Surface", "## Exact/Open Boundary")

    expected = [
        (record.claim_id, [_lean_module_id(path) for path in record.module_paths])
        for record in load_lean_claim_carriers()
    ]

    assert _theorem_surface_claim_module_rows(theorem_surface) == expected
