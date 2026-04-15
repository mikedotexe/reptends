from pathlib import Path

from bridge_reptends.registry import render_proof_system_legend_lines


ROOT = Path(__file__).resolve().parent.parent
AGDA_CORRESPONDENCE = ROOT / "docs" / "AGDA_CORRESPONDENCE.md"


def _marked_block(text: str, start_marker: str, end_marker: str) -> str:
    return text.split(start_marker, 1)[1].split(end_marker, 1)[0].strip()


def test_agda_correspondence_uses_shared_proof_system_legend() -> None:
    text = AGDA_CORRESPONDENCE.read_text()

    assert _marked_block(
        text,
        "<!-- PROOF_SYSTEM_LEGEND_START -->",
        "<!-- PROOF_SYSTEM_LEGEND_END -->",
    ) == "\n".join(render_proof_system_legend_lines())


def test_agda_correspondence_keeps_agda_specific_audit_boundary() -> None:
    text = AGDA_CORRESPONDENCE.read_text()

    assert "Lean is the theorem-complete formal backend for the current" in text
    assert "Future public prose must not imply Agda has full proof parity with Lean" in text
    assert "## Classification Legend" in text
    assert "`locally provable in Agda`" in text
    assert "`intentionally postulated but Lean-backed`" in text
    assert "`open or out of scope`" in text
