from math import lcm

from bridge_reptends import (
    canonical_composite_case_studies,
    canonical_composite_family_case_studies,
    crt_period_profile,
    crt_remainder_orbit,
    preperiod_length,
    prime_power_lifting_family,
    reconstruct_from_crt,
)
from bridge_reptends.analysis import multiplicative_order


def test_preperiod_length_tracks_base_factor_valuations() -> None:
    assert preperiod_length(28, base=10) == 2
    assert preperiod_length(125, base=10) == 3
    assert preperiod_length(996, base=10) == 2


def test_crt_period_profile_matches_lcm_of_component_orders() -> None:
    profile = crt_period_profile(21, base=10)

    assert profile.stripped_modulus == 21
    assert profile.global_order == 6
    assert profile.global_order == multiplicative_order(10, 21)

    component_orders = {component.modulus: component.local_order for component in profile.components}
    assert component_orders == {3: 1, 7: 6}
    assert profile.global_order == lcm(*(component.local_order for component in profile.components))


def test_stripped_composite_profile_keeps_preperiod_and_period_separate() -> None:
    profile = crt_period_profile(996, base=10)

    assert profile.stripped_modulus == 249
    assert profile.preperiod_digits == 2
    assert profile.global_order == multiplicative_order(10, 249)


def test_crt_reconstruction_matches_component_remainders() -> None:
    profile = crt_period_profile(21, base=10)
    rows = crt_remainder_orbit(21, base=10, steps=profile.global_order)

    for row in rows:
        assert reconstruct_from_crt(row.component_remainders, profile.component_moduli) == row.remainder


def test_profile_exposes_lcm_and_carmichael_relations() -> None:
    profile = crt_period_profile(249, base=10)

    assert profile.local_order_lcm == 41
    assert profile.order_equals_component_lcm is True
    assert profile.order_divides_carmichael is True
    assert profile.carmichael_quotient == 2

    summary = "\n".join(profile.summary_lines())
    assert "ord_M(10) = lcm(component orders) = 41" in summary
    assert "lambda(M) = 82" in summary


def test_canonical_composite_case_studies_cover_named_examples() -> None:
    cases = {case.n: case for case in canonical_composite_case_studies()}

    assert {21, 27, 249, 996}.issubset(cases)

    assert cases[21].actual_k == 1
    assert cases[21].profile.carmichael_quotient == 1

    assert cases[27].profile.stripped_modulus == 27
    assert cases[27].profile.carmichael_quotient == 6

    assert cases[249].actual_q == 4
    assert cases[249].core_q == 4
    assert cases[249].profile.global_order == 41

    assert cases[996].profile.stripped_modulus == 249
    assert cases[996].profile.preperiod_digits == 2
    assert cases[996].actual_q == 1
    assert cases[996].core_q == 4
    assert "CRT local data" in cases[249].crt_summary
    assert "preperiod length" in cases[996].preperiod_summary
    assert cases[21].carry_state_count == 1
    assert cases[27].carry_graph_class_count >= 1


def test_prime_power_lifting_family_exposes_stabilization_and_growth() -> None:
    family = prime_power_lifting_family(3, 4, base=10)
    orders = {step.modulus: step.local_order for step in family.steps}

    assert orders == {3: 1, 9: 1, 27: 3, 81: 9}
    assert family.stabilization_exponents == (2,)
    assert family.strict_growth_exponents == (3, 4)
    assert any("stabilized from previous = True" in line for line in family.summary_lines())


def test_canonical_composite_family_case_studies_separate_structures() -> None:
    families = {case.label: case for case in canonical_composite_family_case_studies()}

    lifting = families["Prime-power lifting at p = 3"]
    shared_core = families["Shared periodic core 249 / 996"]

    assert lifting.members == (3, 9, 27, 81)
    assert "local order can stabilize" in lifting.crt_focus
    assert "no stripped base factors" in lifting.preperiod_focus
    assert "order lifting" in lifting.coordinate_focus

    assert shared_core.members == (249, 996)
    assert "same CRT local orders" in shared_core.crt_focus
    assert "only 996 has a preperiod" in shared_core.preperiod_focus
    assert "carry layer changes" in shared_core.carry_focus
