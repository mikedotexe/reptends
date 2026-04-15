from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ORBIT_WEAVE = ROOT / "lean" / "QRTour" / "OrbitWeave.lean"


def _module_doc(text: str) -> str:
    return text.split("/-!", 1)[1].split("-/", 1)[0]


def test_orbit_weave_module_doc_tracks_current_claim_surface() -> None:
    doc = _module_doc(ORBIT_WEAVE.read_text())

    assert "`series_q_weighted_identity`" in doc
    assert "`positive_q_good_modes`" in doc
    assert "body term `W`" in doc
    assert "correction term `F`" in doc
    assert "current scope is deliberately finite" not in doc
    assert "belong in later passes" not in doc
