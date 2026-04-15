from bridge_reptends import load_lean_module_index


def test_claim_tagged_modules_stay_public_claim_surfaces() -> None:
    tagged_modules = [module for module in load_lean_module_index() if module.claim_ids]

    assert tagged_modules
    for module in tagged_modules:
        assert "public example surface" not in module.promotion_decision
        assert "infrastructure" not in module.promotion_decision.lower()
        assert (
            "public theorem surface" in module.promotion_decision
            or "public support surface" in module.promotion_decision
        ), (
            f"{module.id} should remain a public theorem/support surface, got "
            f"{module.promotion_decision!r}"
        )


def test_public_theorem_surface_modules_keep_claim_tags() -> None:
    theorem_surface_modules = [
        module
        for module in load_lean_module_index()
        if "public theorem surface" in module.promotion_decision
    ]

    assert theorem_surface_modules
    assert all(module.claim_ids for module in theorem_surface_modules)


def test_public_example_surface_modules_stay_claim_free_witness_surfaces() -> None:
    example_surface_modules = [
        module
        for module in load_lean_module_index()
        if "public example surface" in module.promotion_decision
    ]

    assert example_surface_modules
    assert all(not module.claim_ids for module in example_surface_modules)
    assert all(
        "witness" in module.current_role.lower() or "example" in module.current_role.lower()
        for module in example_surface_modules
    )


def test_infrastructure_modules_do_not_carry_claim_tags() -> None:
    infrastructure_modules = [
        module
        for module in load_lean_module_index()
        if "infrastructure" in module.promotion_decision.lower()
    ]

    assert infrastructure_modules
    assert all(not module.claim_ids for module in infrastructure_modules)
