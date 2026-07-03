import pytest

from bridge_reptends import registry as registry_module


@pytest.mark.parametrize(
    ("entries", "message"),
    [
        (
            [
                {
                    "id": "QRTour.Basic",
                    "path": "lean/QRTour/Basic.lean",
                    "current_role": "fixture",
                    "promotion_decision": "fixture",
                    "claim_ids": [],
                    "rationale": "fixture",
                },
                {
                    "id": "QRTour.Basic",
                    "path": "lean/QRTour/RemainderOrbit.lean",
                    "current_role": "fixture",
                    "promotion_decision": "fixture",
                    "claim_ids": [],
                    "rationale": "fixture",
                },
            ],
            r"Lean module index ids must be unique, got duplicate 'QRTour\.Basic'",
        ),
        (
            [
                {
                    "id": "QRTour.Basic",
                    "path": "lean/QRTour/Basic.lean",
                    "current_role": "fixture",
                    "promotion_decision": "fixture",
                    "claim_ids": [],
                    "rationale": "fixture",
                },
                {
                    "id": "QRTour.DuplicatePathFixture",
                    "path": "lean/QRTour/Basic.lean",
                    "current_role": "fixture",
                    "promotion_decision": "fixture",
                    "claim_ids": [],
                    "rationale": "fixture",
                },
            ],
            r"Lean module index paths must be unique, got duplicate 'lean/QRTour/Basic\.lean'",
        ),
    ],
)
def test_lean_module_index_loader_rejects_duplicate_public_rows(
    monkeypatch: pytest.MonkeyPatch,
    entries: list[dict[str, object]],
    message: str,
) -> None:
    monkeypatch.setattr(registry_module, "_load_json", lambda filename: entries)

    with pytest.raises(ValueError, match=message):
        registry_module.load_lean_module_index()


def test_lean_claim_carrier_loader_rejects_duplicate_claim_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        registry_module,
        "_load_json",
        lambda filename: [
            {
                "claim_id": "digit_periodicity",
                "module_paths": ["lean/QRTour/Digits.lean"],
                "theorem_names": ["digit_periodic"],
            },
            {
                "claim_id": "digit_periodicity",
                "module_paths": ["lean/QRTour/Digits.lean"],
                "theorem_names": ["digit_remainder_eq"],
            },
        ],
    )

    with pytest.raises(
        ValueError,
        match=r"Lean claim carrier claim ids must be unique, got duplicate 'digit_periodicity'",
    ):
        registry_module.load_lean_claim_carriers()


def test_lean_open_claim_boundary_loader_rejects_duplicate_claim_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        registry_module,
        "_load_json",
        lambda filename: [
            {
                "claim_id": "small_k_visibility_threshold",
                "segments": [
                    {
                        "module_paths": ["lean/QRTour/Visibility.lean"],
                        "summary": "fixture",
                    }
                ],
            },
            {
                "claim_id": "small_k_visibility_threshold",
                "segments": [
                    {
                        "module_paths": ["lean/QRTour/CompositeVisibility.lean"],
                        "summary": "fixture",
                    }
                ],
            },
        ],
    )

    with pytest.raises(
        ValueError,
        match=(
            r"Lean open-claim boundary claim ids must be unique, got duplicate "
            r"'small_k_visibility_threshold'"
        ),
    ):
        registry_module.load_lean_open_claim_boundaries()


def test_lean_worked_example_loader_rejects_duplicate_namespaces(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        registry_module,
        "_load_json",
        lambda filename: [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "duplicate witness fixture one",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            },
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["series_q_weighted_identity"],
                "theorem_names": ["coordinate_series_q_weighted_identity"],
                "current_role": "duplicate witness fixture two",
                "witness_ids": ["series_q_weighted_identity_prime97_stride2"],
            },
        ],
    )

    with pytest.raises(
        ValueError,
        match=r"Lean worked example namespaces must be unique, got duplicate 'QRTour\.Prime97'",
    ):
        registry_module.load_lean_worked_examples()
