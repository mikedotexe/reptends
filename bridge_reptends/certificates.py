"""Lean-shaped empirical certificates for visibility frontier searches.

The Certificate Workbench is intentionally search-facing.  It packages the
current finite-window evidence into flat rows that are easy to inspect, export,
and later translate into Lean hypotheses, without promoting those rows to new
atlas claims.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
from typing import Any, Iterable, Mapping, Sequence

from .transducer import (
    CoefficientConflictWitness,
    ObservedStateMap,
    carry_remainder_comparison,
)
from .visibility import certified_positive_lookahead_state_window_rows


WORKBENCH_CASE_GROUP = "certificate_workbench_case"
WORKBENCH_SUMMARY_GROUP = "certificate_workbench_summary"
OBSERVABILITY_SUMMARY_GROUP = "observability_summary"
OBSERVABILITY_TARGET_SPLIT_SUMMARY_GROUP = "observability_target_split_summary"
OBSERVABILITY_TARGET_SPLIT_CASE_GROUP = "observability_target_split_case"
OBSERVABILITY_TARGET_SIGNATURE_SUMMARY_GROUP = (
    "observability_target_signature_summary"
)
OBSERVABILITY_TARGET_SIGNATURE_FAMILY_GROUP = (
    "observability_target_signature_family"
)
OBSERVABILITY_MOD_STABLE_CARRY_LOSS_SUMMARY_GROUP = (
    "observability_mod_stable_carry_loss_summary"
)
OBSERVABILITY_MOD_STABLE_CARRY_LOSS_CASE_GROUP = (
    "observability_mod_stable_carry_loss_case"
)
OBSERVABILITY_SHAPE13_K4_MOD_STABLE_CARRY_LOSS_SUMMARY_GROUP = (
    "observability_shape13_k4_mod_stable_carry_loss_summary"
)
OBSERVABILITY_SHAPE13_K4_MOD_STABLE_CARRY_LOSS_MEMBER_GROUP = (
    "observability_shape13_k4_mod_stable_carry_loss_member"
)
OBSERVABILITY_INSTRUMENT_SUMMARY_GROUP = "observability_instrument_summary"
OBSERVABILITY_SOURCE_SHAPE_GROUP = "observability_source_symmetry_shape"
OBSERVABILITY_INSTRUMENT_MEMBER_GROUP = "observability_instrument_member"
OBSERVABILITY_SHAPE17_K4_SUMMARY_GROUP = "observability_shape17_k4_family_summary"
OBSERVABILITY_SHAPE17_K4_MEMBER_GROUP = "observability_shape17_k4_family_member"
OBSERVABILITY_NEXT_SOURCE_SHAPE_SUMMARY_GROUP = (
    "observability_next_source_shape_family_summary"
)
OBSERVABILITY_NEXT_SOURCE_SHAPE_MEMBER_GROUP = (
    "observability_next_source_shape_family_member"
)
OBSERVABILITY_SHAPE187_K188_SUMMARY_GROUP = (
    "observability_shape187_k188_family_summary"
)
OBSERVABILITY_SHAPE187_K188_MEMBER_GROUP = (
    "observability_shape187_k188_family_member"
)
OBSERVABILITY_PROGRAM_SUMMARY_GROUP = "observability_program_summary"
OBSERVABILITY_PROGRAM_LANE_GROUP = "observability_program_lane"
OBSERVABILITY_PROGRAM_FAMILY_GROUP = "observability_program_family"
OBSERVABILITY_POSITIVE_RECONSTRUCTION_CANDIDATE_GROUP = (
    "observability_positive_reconstruction_candidate"
)
OBSERVABILITY_PROGRAM_NEXT_TASK_GROUP = "observability_program_next_task"

COMPOSITE68_ANCHOR_KEYS = ((10, 68), (30, 68))
FRONTIER_ANCHOR_KEYS = ((10, 97), (10, 996))
DEFAULT_ANCHOR_KEYS = COMPOSITE68_ANCHOR_KEYS + FRONTIER_ANCHOR_KEYS

CERTIFICATE_LEAN_FIXTURE_SCHEMA = "certificate-lean-fixtures-v1"
CERTIFICATE_LEAN_STUBS_SCHEMA = "certificate-lean-stubs-v1"
CERTIFICATE_FIXTURE_MAPPING_LINT_SCHEMA = "certificate-fixture-mapping-lint-v1"
SOURCE_PINNING_RECIPE_ID = "source_pinning_recipe_v1"
LEAN_FINITE_PACKAGE_PLAN_ID = "lean_finite_package_plan_v1"
DEFAULT_SCAFFOLD_NAMESPACE_PREFIX = "QRTour.Future"
OPEN_BOUNDARY_IDS = ["small_k_visibility_threshold", "carry_dfa_factorization"]
SHAPE13_K4_MOD_STABLE_SOURCE_SYMMETRY_SIGNATURE = (
    "periodic_modulus=13;k=4;position_gap=6"
)
SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE = "periodic_modulus=17;k=4;position_gap=4"
SHAPE187_K188_SOURCE_SYMMETRY_SIGNATURE = "periodic_modulus=187;k=188;position_gap=6"
DEFAULT_SETTLED_SOURCE_SHAPE_SIGNATURES = (SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE,)
SAME_CORE_SHIFT_GENERIC_CRITERION_THEOREM = (
    "sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one"
)
SHAPE13_K4_SCALE_TWO_CRITERION_THEOREM = (
    "sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two"
)
SAME_POSITION_IDEMPOTENT_GENERIC_CRITERION_THEOREM = (
    "samePositionIdempotent_hiddenCarryBlockValue"
)
SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_RECORD = (
    "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses"
)
SAME_POSITION_SCALING_IDEMPOTENT_REMAINDER_PROJECTION = (
    "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder"
)
SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_ADAPTER = (
    "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
)
POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_ID = (
    "finite_remainder_state_injective_on_window"
)
POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_FORMULA = (
    "pairwise_distinct(remainder_state[j] for j in visible_window)"
)
POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_ID = (
    "finite_remainder_power_residue_no_collision"
)
POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_FORMULA = (
    "pairwise_distinct(k^j % n for 0 <= j < requested_blocks)"
)
POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_ID = (
    "finite_remainder_power_residue_no_wrap"
)
POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_FORMULA = (
    "1 < k and k^j < n for 0 <= j < requested_blocks"
)
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_MODULI = [17, 34, 68, 85, 170, 340]
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base7K3PositiveReconstruction.n170_n340_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_MODULI = [109, 218, 1199, 2398]
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_MODULI = [
    59,
    118,
    997,
    1994,
    58823,
    117646,
]
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_MODULI = [
    23,
    55,
    69,
    115,
    155,
    165,
    253,
    345,
    465,
    713,
    759,
    1265,
    1705,
    2139,
    3565,
    3795,
    5115,
    7843,
    10695,
    23529,
    39215,
    117645,
]
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base7Stride6K4PositiveReconstruction.n345_n465_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_MODULI = [23, 69, 299, 897]
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base30K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_MODULI = [
    397,
    794,
    1588,
    6749,
    13498,
    26996,
]
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_MODULI = [83, 166, 249, 332, 498, 996]
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_MODULI = [
    49,
    98,
    119,
    147,
    196,
    238,
    294,
    357,
    476,
    588,
    714,
    833,
]
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base10Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_MODULI = [
    17,
    34,
    173,
    289,
    346,
    578,
    2941,
    5882,
    49997,
    99994,
]
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_PAIR_THEOREM = (
    "QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_MODULI = [
    641,
    1282,
    1923,
    2564,
    3846,
    7692,
    8333,
    16666,
    24999,
    33332,
    49998,
    99996,
]
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base10Stride5K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base10Stride5K4PositiveReconstruction.n641_n1282_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_MODULI = [
    17,
    41,
    51,
    119,
    123,
    287,
    289,
    357,
    697,
    861,
    867,
    2023,
    2091,
    4879,
    6069,
    11849,
    14637,
    35547,
    82943,
    248829,
]
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base12Stride5K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base12Stride5K3PositiveReconstruction.n289_n861_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_MODULI = [47, 141]
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_MODULI = [
    23,
    25,
    69,
    75,
    115,
    345,
    575,
    1725,
]
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_PAIR_THEOREM = (
    "QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_MODULI = [
    71,
    73,
    142,
    146,
    284,
    292,
    5183,
    10366,
    20732,
]
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_CRITERION_STATUS = (
    "lean_proved_explicit_divisor_family_criterion"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_NO_COLLISION_THEOREM = (
    "QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_FUNCTIONAL_THEOREM = (
    "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM = (
    "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
)
POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_PAIR_THEOREM = (
    "QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair"
)
SHAPE17_K4_NAMED_SHIFT_INSTANTIATIONS = {
    (10, 34): "QRTour.Shape17K4.base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift",
    (10, 68): "QRTour.Shape17K4.base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift",
    (30, 34): "QRTour.Shape17K4.base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift",
    (30, 68): "QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift",
}
SHAPE13_K4_NAMED_SHIFT_INSTANTIATIONS = {
    (30, 26): "QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift",
}
SHAPE187_K188_NAMED_SAME_POSITION_INSTANTIATIONS = {
    (
        10,
        374,
    ): "QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
    (
        12,
        374,
    ): "QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
    (
        30,
        374,
    ): "QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
    (
        30,
        748,
    ): "QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
}
SHAPE187_K188_NAMED_SAME_POSITION_HYPOTHESIS_INSTANTIATIONS = {
    (
        10,
        374,
    ): "QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses",
    (
        12,
        374,
    ): "QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses",
    (
        30,
        374,
    ): "QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses",
    (
        30,
        748,
    ): "QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses",
}
SHAPE187_K188_NAMED_FINITE_CONFLICT_INSTANTIATIONS = {
    (
        10,
        374,
    ): "QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two",
    (
        30,
        374,
    ): "QRTour.FutureBase30N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_one",
    (
        30,
        748,
    ): "QRTour.FutureBase30N748.coordinate_stateAlignments_one_two_certifiedConflict_eight_one",
}
SOURCE_PINNED_FIXTURE_STATUS = "source_pinned_existing_theorem"
LEAN_STUB_SCAFFOLD_STATUS = "copyable_projection_stub"
DEFAULT_FIXTURE_RECORD_THEOREM_NAME = (
    "coordinate_stateAlignments_one_five_certifiedConflict_eight_one"
)
DEFAULT_FIXTURE_PROJECTION_ACCESSOR = "not_remainderToCoefficientFunctional"

LEAN_FIXTURE_THEOREM_NAMES = (
    "coordinate_stateAlignments_one_five_certifiedConflict_eight_one",
    "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
    "coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one",
    "coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one",
    "coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one",
)

LEAN_FIXTURE_PROOF_PATH_SNIPPET = (
    "have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one\n"
    "exact hrecord.not_remainderToCoefficientFunctional"
)

LEAN_FIXTURE_ANCHORS = {
    (10, 68): {
        "namespace": "QRTour.Composite68",
        "module_path": "lean/QRTour/Examples.lean",
    },
    (30, 68): {
        "namespace": "QRTour.Composite68Base30",
        "module_path": "lean/QRTour/Examples.lean",
    },
}

POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS = {
    (10, 97): {
        "namespace": "QRTour.Prime97",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        ),
    },
    (10, 98): {
        "namespace": "QRTour.FutureBase10N98",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (12, 142): {
        "namespace": "QRTour.FutureBase12N142",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 47): {
        "namespace": "QRTour.FutureBase7N47",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (12, 71): {
        "namespace": "QRTour.FutureBase12N71",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 49): {
        "namespace": "QRTour.FutureBase10N49",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (30, 299): {
        "namespace": "QRTour.FutureBase30N299",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 170): {
        "namespace": "QRTour.FutureBase7N170",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 997): {
        "namespace": "QRTour.FutureBase10N997",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (12, 575): {
        "namespace": "QRTour.FutureBase12N575",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 1199): {
        "namespace": "QRTour.FutureBase7N1199",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 294): {
        "namespace": "QRTour.FutureBase10N294",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 46): {
        "namespace": "QRTour.FutureBase7N46",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        ),
    },
    (12, 47): {
        "namespace": "QRTour.FutureBase12N47",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        ),
    },
    (7, 141): {
        "namespace": "QRTour.FutureBase7N141",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (12, 146): {
        "namespace": "QRTour.FutureBase12N146",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 769): {
        "namespace": "QRTour.FutureBase10N769",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 345): {
        "namespace": "QRTour.FutureBase7N345",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 542): {
        "namespace": "QRTour.FutureBase7N542",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (30, 794): {
        "namespace": "QRTour.FutureBase30N794",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 113): {
        "namespace": "QRTour.FutureBase7N113",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        ),
    },
    (12, 691): {
        "namespace": "QRTour.FutureBase12N691",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (12, 226): {
        "namespace": "QRTour.FutureBase12N226",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 338): {
        "namespace": "QRTour.FutureBase7N338",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        ),
    },
    (12, 149): {
        "namespace": "QRTour.FutureBase12N149",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 578): {
        "namespace": "QRTour.FutureBase10N578",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 277): {
        "namespace": "QRTour.FutureBase10N277",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 669): {
        "namespace": "QRTour.FutureBase7N669",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 71): {
        "namespace": "QRTour.FutureBase7N71",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (7, 118): {
        "namespace": "QRTour.FutureBase7N118",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
    (10, 996): {
        "namespace": "QRTour.Composite996",
        "module_path": "lean/QRTour/Examples.lean",
        "functional_theorem_name": (
            "actual996_stateAlignments_remainderToCoefficientFunctional_eight_one"
        ),
        "factor_through_theorem_name": (
            "actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        ),
    },
}

CERTIFICATE_CLASS_ORDER = {
    "lean_ready_hidden_conflict": 0,
    "gap_one_bridge_candidate": 1,
    "hidden_conflict_frontier": 2,
    "visible_conflict_frontier": 3,
    "functional_frontier": 4,
}

OBSERVABILITY_GROUP_BY_CERTIFICATE_CLASS = {
    "lean_ready_hidden_conflict": "hidden_coefficient_conflict",
    "hidden_conflict_frontier": "hidden_coefficient_conflict",
    "visible_conflict_frontier": "visible_coefficient_conflict",
    "functional_frontier": "coefficient_functional_frontier",
    "gap_one_bridge_candidate": "gap_one_bridge_candidate",
}

OBSERVABILITY_GROUP_ORDER = {
    "hidden_coefficient_conflict": 0,
    "visible_coefficient_conflict": 2,
    "coefficient_functional_frontier": 3,
    "gap_one_bridge_candidate": 4,
}

OBSERVABILITY_TARGET_IDS = (
    "raw_coefficient_nat",
    "coefficient_mod_block_base",
    "carried_block_value",
    "carry_state",
    "remainder_state",
    "displayed_prefix",
)

OBSERVABILITY_MAP_TARGETS = {
    "raw_coefficient_nat": {
        "prefix": "remainder_to_coefficient",
        "observation_kind": "remainder_state",
        "signal_kind": "raw_coefficient_nat",
        "factor_through_surface": "remainder_state_to_raw_coefficient_nat",
    },
    "coefficient_mod_block_base": {
        "prefix": "remainder_to_coefficient_mod_block_base",
        "observation_kind": "remainder_state",
        "signal_kind": "coefficient_mod_block_base",
        "factor_through_surface": "remainder_state_to_coefficient_mod_block_base",
    },
    "carried_block_value": {
        "prefix": "remainder_to_carried_block_value",
        "observation_kind": "remainder_state",
        "signal_kind": "carried_block_value",
        "factor_through_surface": "remainder_state_to_carried_block_value",
    },
    "carry_state": {
        "prefix": "remainder_to_carry",
        "observation_kind": "remainder_state",
        "signal_kind": "carry_state",
        "factor_through_surface": "remainder_state_to_carry_state",
    },
}

OBSERVABILITY_TARGET_SIGNATURE_CLASS_ORDER = {
    "raw_coefficient_obstructed_carried_output_hidden": 0,
    "raw_and_mod_block_base_obstructed": 1,
    "carry_state_first_loss": 2,
    "mixed_target_loss_frontier": 3,
    "all_pointwise_targets_functional_frontier": 4,
    "gap_one_bridge_signature": 5,
}

MOD_STABLE_CARRY_LOSS_SIGNATURE = (
    "raw_coefficient_nat:factor_through_obstructed | "
    "coefficient_mod_block_base:factor_through_candidate | "
    "carried_block_value:functional_output_hides_raw_coefficient_conflict | "
    "carry_state:factor_through_obstructed | "
    "remainder_state:identity_observation | "
    "displayed_prefix:certified_window_output_agreement"
)

@dataclass(frozen=True)
class LookaheadCertificate:
    """Flat positive-lookahead certificate data for one finite window."""

    requested_blocks: int
    certified_lookahead_blocks: int
    lookahead_lower_bound: int
    exact_gap_numerator: int
    lookahead_certificate_matches: bool

    @classmethod
    def from_row(cls, row: Mapping[str, Any]) -> "LookaheadCertificate":
        return cls(
            requested_blocks=int(row["requested_blocks"]),
            certified_lookahead_blocks=int(row["certified_lookahead_blocks"]),
            lookahead_lower_bound=int(row["lookahead_lower_bound"]),
            exact_gap_numerator=int(row["exact_gap_numerator"]),
            lookahead_certificate_matches=bool(row["lookahead_certificate_matches"]),
        )

    def to_row(self) -> dict[str, Any]:
        return {
            "requested_blocks": self.requested_blocks,
            "certified_lookahead_blocks": self.certified_lookahead_blocks,
            "lookahead_lower_bound": self.lookahead_lower_bound,
            "exact_gap_numerator": self.exact_gap_numerator,
            "lookahead_certificate_matches": self.lookahead_certificate_matches,
        }


@dataclass(frozen=True)
class StateMapCertificate:
    """Flat diagnostics for an observed finite state map."""

    functional: bool
    injective: bool
    fiber_signature: str
    ambiguity_signature: str
    ambiguous_sources: list[int]
    ambiguous_targets: list[list[int]]

    @classmethod
    def from_state_map(cls, state_map: ObservedStateMap) -> "StateMapCertificate":
        exported = state_map.export()
        ambiguous_sources = [
            int(entry["source_state"])
            if isinstance(entry, Mapping)
            else int(entry)
            for entry in exported.get("ambiguous_sources", [])
        ]
        ambiguous_targets_by_source = {
            int(fiber["source_state"]): [
                int(target) for target in fiber.get("target_states", [])
            ]
            for fiber in exported.get("fibers", [])
            if isinstance(fiber, Mapping)
        }
        return cls(
            functional=bool(exported["is_functional"]),
            injective=bool(exported["is_injective"]),
            fiber_signature=str(exported["fiber_signature"]),
            ambiguity_signature=str(exported["ambiguity_signature"]),
            ambiguous_sources=ambiguous_sources,
            ambiguous_targets=[
                ambiguous_targets_by_source.get(source, [])
                for source in ambiguous_sources
            ],
        )

    def to_row(self, prefix: str) -> dict[str, Any]:
        return {
            f"{prefix}_functional": self.functional,
            f"{prefix}_injective": self.injective,
            f"{prefix}_fiber_signature": self.fiber_signature,
            f"{prefix}_ambiguity_signature": self.ambiguity_signature,
            f"{prefix}_ambiguous_sources": self.ambiguous_sources,
            f"{prefix}_ambiguous_targets": self.ambiguous_targets,
        }


CONFLICT_FIELD_NAMES = (
    "conflict_remainder_state",
    "conflict_positions",
    "conflict_coefficients",
    "conflict_carry_states",
    "conflict_block_values",
    "conflict_output_hidden",
    "conflict_position_gap",
    "conflict_coefficient_delta",
)


@dataclass(frozen=True)
class CoefficientConflictCertificate:
    """A first finite conflict for remainder-to-coefficient functionality."""

    remainder_state: int
    positions: tuple[int, int]
    coefficients: tuple[int, int]
    carry_states: tuple[int, int]
    block_values: tuple[int, int]
    position_gap: int
    coefficient_delta: int
    output_hidden: bool

    @classmethod
    def from_witness(
        cls, witness: CoefficientConflictWitness
    ) -> "CoefficientConflictCertificate":
        return cls(
            remainder_state=int(witness.remainder_state),
            positions=(int(witness.positions[0]), int(witness.positions[1])),
            coefficients=(
                int(witness.coefficients[0]),
                int(witness.coefficients[1]),
            ),
            carry_states=(
                int(witness.carry_states[0]),
                int(witness.carry_states[1]),
            ),
            block_values=(
                int(witness.block_values[0]),
                int(witness.block_values[1]),
            ),
            position_gap=int(witness.position_gap),
            coefficient_delta=int(witness.coefficient_delta),
            output_hidden=bool(witness.output_hidden),
        )

    @staticmethod
    def empty_row() -> dict[str, Any]:
        return {field_name: None for field_name in CONFLICT_FIELD_NAMES}

    def to_row(self) -> dict[str, Any]:
        return {
            "conflict_remainder_state": self.remainder_state,
            "conflict_positions": list(self.positions),
            "conflict_coefficients": list(self.coefficients),
            "conflict_carry_states": list(self.carry_states),
            "conflict_block_values": list(self.block_values),
            "conflict_output_hidden": self.output_hidden,
            "conflict_position_gap": self.position_gap,
            "conflict_coefficient_delta": self.coefficient_delta,
        }


def _state_alignment_window_fields(comparison: Any) -> dict[str, Any]:
    positions = [int(alignment.position) for alignment in comparison.alignments]
    remainder_states = [
        int(alignment.remainder_state) for alignment in comparison.alignments
    ]
    coefficients = [int(alignment.coefficient) for alignment in comparison.alignments]
    carry_states = [int(alignment.carry_state) for alignment in comparison.alignments]

    positions_by_remainder: dict[int, list[int]] = {}
    for position, remainder_state in zip(positions, remainder_states):
        positions_by_remainder.setdefault(remainder_state, []).append(position)
    repeated = {
        remainder_state: positions
        for remainder_state, positions in sorted(positions_by_remainder.items())
        if len(positions) > 1
    }
    repeat_signature = (
        "injective"
        if not repeated
        else " | ".join(
            f"{remainder_state}@{','.join(str(position) for position in positions)}"
            for remainder_state, positions in repeated.items()
        )
    )

    return {
        "state_alignment_positions": positions,
        "remainder_state_window": remainder_states,
        "raw_coefficient_window": coefficients,
        "carry_state_window": carry_states,
        "remainder_state_window_distinct_count": len(positions_by_remainder),
        "remainder_state_window_injective": len(positions_by_remainder)
        == len(remainder_states),
        "remainder_state_window_repeat_signature": repeat_signature,
    }


@dataclass(frozen=True)
class CertificateWorkbenchRecord:
    """One flat, exportable Certificate Workbench case."""

    base_row: Mapping[str, Any]
    lookahead: LookaheadCertificate
    remainder_to_coefficient: StateMapCertificate
    remainder_to_coefficient_mod_block_base: StateMapCertificate
    remainder_to_carried_block_value: StateMapCertificate
    remainder_to_carry: StateMapCertificate
    carry_to_remainder: StateMapCertificate
    state_alignment_window: Mapping[str, Any]
    conflict: CoefficientConflictCertificate | None
    certificate_class: str
    lean_readiness: str
    next_lean_task: str

    def to_row(self) -> dict[str, Any]:
        core_keys = (
            "n",
            "periodic_modulus",
            "base",
            "m",
            "B",
            "q",
            "k",
            "period",
            "preperiod_digits",
            "lookahead_blocks",
            "obstruction_class",
            "theorem_frontier_status",
        )
        row = {
            "group": WORKBENCH_CASE_GROUP,
            "certificate_id": (
                f"base{int(self.base_row['base'])}_n{int(self.base_row['n'])}"
                f"_m{int(self.base_row['m'])}_blocks{self.lookahead.requested_blocks}"
                f"_L{self.lookahead.certified_lookahead_blocks}"
            ),
        }
        for key in core_keys:
            if key in self.base_row:
                row[key] = self.base_row[key]
        row.update(self.lookahead.to_row())
        row.update(dict(self.state_alignment_window))
        row.update(
            self.remainder_to_coefficient.to_row("remainder_to_coefficient")
        )
        row.update(
            self.remainder_to_coefficient_mod_block_base.to_row(
                "remainder_to_coefficient_mod_block_base"
            )
        )
        row.update(
            self.remainder_to_carried_block_value.to_row(
                "remainder_to_carried_block_value"
            )
        )
        row.update(self.remainder_to_carry.to_row("remainder_to_carry"))
        row.update(self.carry_to_remainder.to_row("carry_to_remainder"))
        if self.conflict is None:
            row.update(CoefficientConflictCertificate.empty_row())
        else:
            row.update(self.conflict.to_row())
        row.update(
            {
                "certificate_class": self.certificate_class,
                "lean_readiness": self.lean_readiness,
                "next_lean_task": self.next_lean_task,
            }
        )
        return row


def _parse_bases(bases: Iterable[int]) -> tuple[int, ...]:
    parsed = tuple(int(base) for base in bases)
    if not parsed:
        raise ValueError("at least one base is required")
    return parsed


def _is_composite68_family_record(
    row: Mapping[str, Any], conflict: CoefficientConflictCertificate | None
) -> bool:
    return (
        int(row["n"]) == 68
        and int(row["k"]) == 4
        and int(row["B"]) % 68 == 4
        and conflict is not None
        and conflict.output_hidden
        and conflict.positions == (1, 5)
        and conflict.carry_states == (0, 60)
        and conflict.block_values[0] == conflict.block_values[1]
    )


def _classify_record(
    row: Mapping[str, Any], conflict: CoefficientConflictCertificate | None
) -> tuple[str, str, str]:
    if (
        row.get("theorem_frontier_status") == "covered_by_gap_one_bridge"
        or int(row["exact_gap_numerator"]) == 1
    ):
        return (
            "gap_one_bridge_candidate",
            "gap_one_bridge_candidate",
            "extend_gap_one_bridge",
        )
    if _is_composite68_family_record(row, conflict):
        return (
            "lean_ready_hidden_conflict",
            "existing_composite68_family_theorem",
            "reuse_composite68_family_certificate",
        )
    if conflict is not None and conflict.output_hidden:
        return (
            "hidden_conflict_frontier",
            "needs_finite_example_package",
            "mine_hidden_conflict_family_or_add_finite_package",
        )
    if conflict is not None:
        return (
            "visible_conflict_frontier",
            "needs_finite_example_package",
            "add_finite_conflict_package_or_refine_state_map",
        )
    return (
        "functional_frontier",
        "empirical_frontier_only",
        "search_arithmetic_functionality_criterion",
    )


def _record_sort_key(row: Mapping[str, Any]) -> tuple[int, int, int, int, int, int]:
    return (
        CERTIFICATE_CLASS_ORDER[str(row["certificate_class"])],
        int(row["exact_gap_numerator"]),
        int(row["certified_lookahead_blocks"]),
        int(row["k"]),
        int(row["n"]),
        int(row["base"]),
    )


def _select_with_anchors(
    rows: Sequence[dict[str, Any]], top: int, anchors: Sequence[tuple[int, int]]
) -> list[dict[str, Any]]:
    if top and top > 0:
        selected = list(rows[:top])
    else:
        selected = list(rows)
    selected_keys = {(int(row["base"]), int(row["n"])) for row in selected}
    for base, n in anchors:
        if (base, n) in selected_keys:
            continue
        for row in rows:
            if int(row["base"]) == base and int(row["n"]) == n:
                selected.append(row)
                selected_keys.add((base, n))
                break
    return selected


def _summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_rows: Sequence[dict[str, Any]],
    emitted_rows: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    lean_ready_rows = [
        row
        for row in all_rows
        if row["lean_readiness"] == "existing_composite68_family_theorem"
    ]
    hidden_conflict_rows = [
        row
        for row in all_rows
        if row["certificate_class"]
        in {"lean_ready_hidden_conflict", "hidden_conflict_frontier"}
    ]
    functional_rows = [
        row for row in all_rows if row["certificate_class"] == "functional_frontier"
    ]
    gap_one_rows = [
        row
        for row in all_rows
        if row["certificate_class"] == "gap_one_bridge_candidate"
    ]
    if lean_ready_rows:
        recommended = "reuse_composite68_family_certificate"
    elif gap_one_rows:
        recommended = "extend_gap_one_bridge"
    elif hidden_conflict_rows:
        recommended = "mine_hidden_conflict_family_or_add_finite_package"
    else:
        recommended = "search_arithmetic_functionality_criterion"
    first_lean_ready_tuple = None
    if lean_ready_rows:
        first = lean_ready_rows[0]
        first_lean_ready_tuple = [
            int(first["base"]),
            int(first["n"]),
            int(first["m"]),
            int(first["B"]),
            int(first["q"]),
            int(first["k"]),
            int(first["certified_lookahead_blocks"]),
            int(first["exact_gap_numerator"]),
        ]
    return {
        "group": WORKBENCH_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "total_cases": len(all_rows),
        "emitted_cases": len(emitted_rows),
        "lean_ready_cases": len(lean_ready_rows),
        "hidden_conflict_cases": len(hidden_conflict_rows),
        "functional_frontier_cases": len(functional_rows),
        "first_lean_ready_tuple": first_lean_ready_tuple,
        "recommended_next_lean_task": recommended,
    }


def certificate_workbench_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Return flat Certificate Workbench rows for empirical frontier triage."""

    parsed_bases = _parse_bases(bases)
    case_rows: list[dict[str, Any]] = []
    for base in parsed_bases:
        state_rows = certified_positive_lookahead_state_window_rows(
            max_n=max_n,
            base=base,
            n_blocks=n_blocks,
            max_lookahead_blocks=max_lookahead_blocks,
        )
        for state_row in state_rows:
            if state_row.get("group") != "certified_positive_lookahead_case":
                continue
            comparison = carry_remainder_comparison(
                int(state_row["n"]),
                base=int(state_row["base"]),
                n_blocks=int(state_row["requested_blocks"]),
                prefer_m=int(state_row["m"]),
                max_lookahead_blocks=max_lookahead_blocks,
            )
            conflict_witness = comparison.first_remainder_to_coefficient_conflict
            conflict = (
                CoefficientConflictCertificate.from_witness(conflict_witness)
                if conflict_witness is not None
                else None
            )
            certificate_class, lean_readiness, next_lean_task = _classify_record(
                state_row, conflict
            )
            record = CertificateWorkbenchRecord(
                base_row=state_row,
                lookahead=LookaheadCertificate.from_row(state_row),
                remainder_to_coefficient=StateMapCertificate.from_state_map(
                    comparison.remainder_to_coefficient_map
                ),
                remainder_to_coefficient_mod_block_base=StateMapCertificate.from_state_map(
                    comparison.remainder_to_coefficient_mod_block_base_map
                ),
                remainder_to_carried_block_value=StateMapCertificate.from_state_map(
                    comparison.remainder_to_carried_block_value_map
                ),
                remainder_to_carry=StateMapCertificate.from_state_map(
                    comparison.remainder_to_carry_map
                ),
                carry_to_remainder=StateMapCertificate.from_state_map(
                    comparison.carry_to_remainder_map
                ),
                state_alignment_window=_state_alignment_window_fields(comparison),
                conflict=conflict,
                certificate_class=certificate_class,
                lean_readiness=lean_readiness,
                next_lean_task=next_lean_task,
            )
            case_rows.append(record.to_row())
    case_rows.sort(key=_record_sort_key)
    emitted_rows = _select_with_anchors(case_rows, top, DEFAULT_ANCHOR_KEYS)
    return [
        _summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_rows=case_rows,
            emitted_rows=emitted_rows,
        ),
        *emitted_rows,
    ]


def _observability_group_for_row(row: Mapping[str, Any]) -> str:
    return OBSERVABILITY_GROUP_BY_CERTIFICATE_CLASS[str(row["certificate_class"])]


def _observability_status_for_row(row: Mapping[str, Any]) -> str:
    certificate_class = str(row["certificate_class"])
    if certificate_class == "lean_ready_hidden_conflict":
        return "lean_proved_finite_hidden_obstruction_existing_theorem"
    if certificate_class == "hidden_conflict_frontier":
        return "empirical_hidden_obstruction_frontier_open_boundary"
    if certificate_class == "visible_conflict_frontier":
        return "empirical_visible_conflict_frontier_open_boundary"
    if certificate_class == "functional_frontier":
        return "empirical_coefficient_functional_frontier_open_boundary"
    return "empirical_gap_one_bridge_candidate_open_boundary"


def _next_observability_task_for_row(row: Mapping[str, Any]) -> str:
    certificate_class = str(row["certificate_class"])
    if certificate_class == "lean_ready_hidden_conflict":
        return "develop_composite68_observability_flagship"
    if certificate_class == "hidden_conflict_frontier":
        return "mine_hidden_conflict_family_or_add_finite_package"
    if certificate_class == "visible_conflict_frontier":
        return "compare_visible_conflict_instrument_behavior"
    if certificate_class == "functional_frontier":
        return "search_positive_coefficient_reconstruction_criterion"
    return "extend_gap_one_observability_bridge"


def _target_hides_raw_conflict(row: Mapping[str, Any], target_id: str) -> bool:
    return (
        target_id == "carried_block_value"
        and row.get("conflict_remainder_state") is not None
        and bool(row.get("conflict_output_hidden"))
        and not bool(row.get("remainder_to_coefficient_functional"))
    )


def _map_target_status(row: Mapping[str, Any], target_id: str) -> str:
    spec = OBSERVABILITY_MAP_TARGETS[target_id]
    prefix = str(spec["prefix"])
    functional = bool(row[f"{prefix}_functional"])
    if _target_hides_raw_conflict(row, target_id):
        return "functional_output_hides_raw_coefficient_conflict"
    if functional:
        return "factor_through_candidate"
    return "factor_through_obstructed"


def _target_lean_support_status(row: Mapping[str, Any], target_id: str) -> str:
    lean_ready = row.get("lean_readiness") == "existing_composite68_family_theorem"
    if target_id == "raw_coefficient_nat" and lean_ready and not bool(
        row.get("remainder_to_coefficient_functional")
    ):
        return "existing_composite68_full_window_factor_through_obstruction"
    if target_id == "carried_block_value" and lean_ready and _target_hides_raw_conflict(
        row, target_id
    ):
        return "existing_composite68_hidden_output_record"
    if target_id == "displayed_prefix" and bool(row.get("lookahead_certificate_matches")):
        return "existing_finite_window_certificate_support"
    if target_id == "remainder_state":
        return "identity_observation_baseline"
    return "empirical_frontier_only"


def _next_target_task(row: Mapping[str, Any], target_id: str, status: str) -> str:
    if target_id == "raw_coefficient_nat" and status == "factor_through_obstructed":
        if row.get("lean_readiness") == "existing_composite68_family_theorem":
            return "cite_full_window_factor_through_obstruction"
        return "add_or_mine_finite_factor_through_obstruction"
    if target_id == "coefficient_mod_block_base":
        if status == "factor_through_obstructed":
            return "compare_mod_block_base_information_loss"
        return "search_mod_block_base_reconstruction_criterion"
    if target_id == "carried_block_value":
        if status == "functional_output_hides_raw_coefficient_conflict":
            return "classify_hidden_output_normalization"
        return "compare_carried_output_readout"
    if target_id == "carry_state":
        if status == "factor_through_obstructed":
            return "classify_remainder_to_carry_state_failure"
        return "search_remainder_to_carry_state_reconstruction"
    if target_id == "remainder_state":
        return "use_as_observation_baseline"
    return "separate_window_certificate_from_pointwise_targets"


def _observability_target_case_row(
    row: Mapping[str, Any], target_id: str
) -> dict[str, Any]:
    common_keys = (
        "n",
        "periodic_modulus",
        "base",
        "m",
        "B",
        "q",
        "k",
        "period",
        "preperiod_digits",
        "requested_blocks",
        "certified_lookahead_blocks",
        "lookahead_lower_bound",
        "exact_gap_numerator",
        "lookahead_certificate_matches",
        "certificate_id",
        "certificate_class",
        "lean_readiness",
        "coefficient_observability_class",
        "observability_rank",
        "open_boundary_ids",
    )
    exported = {
        "group": OBSERVABILITY_TARGET_SPLIT_CASE_GROUP,
        "observability_target_id": target_id,
    }
    for key in common_keys:
        if key in row:
            exported[key] = row[key]

    if target_id in OBSERVABILITY_MAP_TARGETS:
        spec = OBSERVABILITY_MAP_TARGETS[target_id]
        prefix = str(spec["prefix"])
        status = _map_target_status(row, target_id)
        exported.update(
            {
                "observation_kind": spec["observation_kind"],
                "signal_kind": spec["signal_kind"],
                "target_observability_status": status,
                "target_functional": bool(row[f"{prefix}_functional"]),
                "target_fiber_signature": row[f"{prefix}_fiber_signature"],
                "target_ambiguity_signature": row[f"{prefix}_ambiguity_signature"],
                "target_hides_raw_coefficient_conflict": _target_hides_raw_conflict(
                    row, target_id
                ),
                "factor_through_surface": spec["factor_through_surface"],
                "lean_support_status": _target_lean_support_status(row, target_id),
                "next_target_task": _next_target_task(row, target_id, status),
            }
        )
        return exported

    if target_id == "remainder_state":
        status = "identity_observation"
        exported.update(
            {
                "observation_kind": "remainder_state",
                "signal_kind": "remainder_state",
                "target_observability_status": status,
                "target_functional": True,
                "target_fiber_signature": "identity",
                "target_ambiguity_signature": "identity",
                "target_hides_raw_coefficient_conflict": False,
                "factor_through_surface": "identity_observation",
                "lean_support_status": _target_lean_support_status(row, target_id),
                "next_target_task": _next_target_task(row, target_id, status),
            }
        )
        return exported

    status = (
        "certified_window_output_agreement"
        if bool(row.get("lookahead_certificate_matches"))
        else "uncertified_window_output_agreement"
    )
    exported.update(
        {
            "observation_kind": "finite_displayed_prefix",
            "signal_kind": "displayed_prefix",
            "target_observability_status": status,
            "target_functional": None,
            "target_fiber_signature": None,
            "target_ambiguity_signature": None,
            "target_hides_raw_coefficient_conflict": False,
            "factor_through_surface": "window_level_certificate_not_pointwise_factor_through",
            "lean_support_status": _target_lean_support_status(row, target_id),
            "next_target_task": _next_target_task(row, target_id, status),
        }
    )
    return exported


def _observability_target_case_rows(row: Mapping[str, Any]) -> list[dict[str, Any]]:
    return [
        _observability_target_case_row(row, target_id)
        for target_id in OBSERVABILITY_TARGET_IDS
    ]


def _observability_target_summary_fields(row: Mapping[str, Any]) -> dict[str, Any]:
    target_rows = _observability_target_case_rows(row)
    fields: dict[str, Any] = {
        "observability_targets": list(OBSERVABILITY_TARGET_IDS),
        "observability_target_summary_signature": " | ".join(
            f"{target['observability_target_id']}:{target['target_observability_status']}"
            for target in target_rows
        ),
    }
    for target in target_rows:
        target_id = str(target["observability_target_id"])
        fields[f"{target_id}_observability_status"] = target[
            "target_observability_status"
        ]
        fields[f"{target_id}_functional"] = target["target_functional"]
    return fields


def _same_core_shift_default_fields(row: Mapping[str, Any]) -> dict[str, Any]:
    conflict_present = row.get("conflict_remainder_state") is not None
    hidden_conflict = (
        conflict_present
        and bool(row.get("conflict_output_hidden"))
        and not bool(row.get("remainder_to_coefficient_functional"))
    )
    if hidden_conflict:
        return {
            "same_core_shift_support_status": "finite_only_hidden_conflict",
            "same_core_shift_proof_surface": "finite_conflict_record_only",
            "same_core_shift_scale": None,
            "same_core_shift_source_positions": None,
            "same_core_shift_target_positions": list(row.get("conflict_positions") or []),
            "same_core_hyp_base_prime_support_times_scale_eq_k": None,
            "same_core_hyp_scaled_quotient_remainder_lt_gap": None,
            "same_core_hyp_scaled_block_remainder_lt_block_base": None,
            "same_core_shift_criterion_theorem": None,
            "same_core_shift_named_instantiation": None,
            "same_core_shift_failure_reason": "outside_same_core_shift_classifier",
        }
    return {
        "same_core_shift_support_status": "not_same_core_shift_case",
        "same_core_shift_proof_surface": "none",
        "same_core_shift_scale": None,
        "same_core_shift_source_positions": None,
        "same_core_shift_target_positions": None,
        "same_core_hyp_base_prime_support_times_scale_eq_k": None,
        "same_core_hyp_scaled_quotient_remainder_lt_gap": None,
        "same_core_hyp_scaled_block_remainder_lt_block_base": None,
        "same_core_shift_criterion_theorem": None,
        "same_core_shift_named_instantiation": None,
        "same_core_shift_failure_reason": "not_hidden_coefficient_conflict",
    }


def _observability_row(row: Mapping[str, Any]) -> dict[str, Any]:
    group = _observability_group_for_row(row)
    conflict_present = row.get("conflict_remainder_state") is not None
    output_hidden = bool(row.get("conflict_output_hidden")) if conflict_present else False
    coefficient_information_lost = (
        conflict_present
        and not bool(row.get("remainder_to_coefficient_functional"))
    )
    exported = dict(row)
    exported.update(
        {
            "group": group,
            "coefficient_observability_class": group,
            "observability_boundary_status": _observability_status_for_row(row),
            "source_symmetry_visible": conflict_present,
            "coefficient_information_lost": coefficient_information_lost,
            "carry_output_hides_conflict": output_hidden,
            "next_observability_task": _next_observability_task_for_row(row),
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            **_same_core_shift_default_fields(row),
        }
    )
    exported.update(_observability_target_summary_fields(exported))
    return exported


def _observability_sort_key(row: Mapping[str, Any]) -> tuple[int, int, int, int, int, int]:
    group = str(row["coefficient_observability_class"])
    group_rank = OBSERVABILITY_GROUP_ORDER[group]
    if (
        group == "hidden_coefficient_conflict"
        and row["lean_readiness"] != "existing_composite68_family_theorem"
    ):
        group_rank = 1
    return (
        group_rank,
        int(row["exact_gap_numerator"]),
        int(row["certified_lookahead_blocks"]),
        int(row["k"]),
        int(row["n"]),
        int(row["base"]),
    )


def _observability_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_rows: Sequence[dict[str, Any]],
    emitted_rows: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    hidden_rows = [
        row
        for row in all_rows
        if row["coefficient_observability_class"] == "hidden_coefficient_conflict"
    ]
    lean_ready_hidden_rows = [
        row
        for row in hidden_rows
        if row["lean_readiness"] == "existing_composite68_family_theorem"
    ]
    visible_rows = [
        row
        for row in all_rows
        if row["coefficient_observability_class"] == "visible_coefficient_conflict"
    ]
    functional_rows = [
        row
        for row in all_rows
        if row["coefficient_observability_class"] == "coefficient_functional_frontier"
    ]
    gap_one_rows = [
        row
        for row in all_rows
        if row["coefficient_observability_class"] == "gap_one_bridge_candidate"
    ]
    if lean_ready_hidden_rows:
        recommended = "develop_composite68_observability_flagship"
    elif hidden_rows:
        recommended = "mine_hidden_conflict_family_or_add_finite_package"
    elif visible_rows:
        recommended = "compare_visible_conflict_instrument_behavior"
    elif functional_rows:
        recommended = "search_positive_coefficient_reconstruction_criterion"
    else:
        recommended = "extend_gap_one_observability_bridge"
    first_hidden_tuple = None
    if hidden_rows:
        first = hidden_rows[0]
        first_hidden_tuple = [
            int(first["base"]),
            int(first["n"]),
            int(first["m"]),
            int(first["B"]),
            int(first["q"]),
            int(first["k"]),
            int(first["certified_lookahead_blocks"]),
            int(first["exact_gap_numerator"]),
        ]
    return {
        "group": OBSERVABILITY_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "total_cases": len(all_rows),
        "emitted_cases": len(emitted_rows),
        "hidden_coefficient_conflict_cases": len(hidden_rows),
        "lean_ready_hidden_conflict_cases": len(lean_ready_hidden_rows),
        "visible_coefficient_conflict_cases": len(visible_rows),
        "coefficient_functional_frontier_cases": len(functional_rows),
        "gap_one_bridge_candidate_cases": len(gap_one_rows),
        "same_core_shift_proved_cases": sum(
            1
            for row in all_rows
            if row.get("same_core_shift_support_status")
            == "same_core_shift_proved_by_arithmetic_criterion"
        ),
        "finite_only_hidden_conflict_cases": sum(
            1
            for row in all_rows
            if row.get("same_core_shift_support_status") == "finite_only_hidden_conflict"
        ),
        "first_hidden_conflict_tuple": first_hidden_tuple,
        "recommended_next_observability_task": recommended,
        "observability_boundary_status": "empirical_open_boundary_tooling",
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_atlas_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 50,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Return empirical observability-boundary rows from Certificate Workbench data."""

    parsed_bases = _parse_bases(bases)
    workbench_rows = certificate_workbench_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    case_rows = [
        _observability_row(row)
        for row in workbench_rows
        if row.get("group") == WORKBENCH_CASE_GROUP
    ]
    case_rows.sort(key=_observability_sort_key)
    emitted_rows = _select_with_anchors(case_rows, top, DEFAULT_ANCHOR_KEYS)
    for rank, row in enumerate(emitted_rows, start=1):
        row["observability_rank"] = rank
    return [
        _observability_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_rows=case_rows,
            emitted_rows=emitted_rows,
        ),
        *emitted_rows,
    ]


def _observability_target_split_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    atlas_case_rows: Sequence[dict[str, Any]],
    target_rows: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    obstructed_rows = [
        row
        for row in target_rows
        if row["target_observability_status"] == "factor_through_obstructed"
    ]
    hidden_rows = [
        row
        for row in target_rows
        if bool(row["target_hides_raw_coefficient_conflict"])
    ]
    window_rows = [
        row
        for row in target_rows
        if row["observability_target_id"] == "displayed_prefix"
    ]
    first_tuple = None
    if target_rows:
        first = target_rows[0]
        first_tuple = [
            int(first["base"]),
            int(first["n"]),
            int(first["m"]),
            int(first["B"]),
            int(first["q"]),
            int(first["k"]),
            int(first["certified_lookahead_blocks"]),
            int(first["exact_gap_numerator"]),
        ]
    return {
        "group": OBSERVABILITY_TARGET_SPLIT_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "atlas_cases": len(atlas_case_rows),
        "target_rows": len(target_rows),
        "observability_targets": list(OBSERVABILITY_TARGET_IDS),
        "factor_through_obstructed_target_rows": len(obstructed_rows),
        "raw_conflict_hidden_by_target_rows": len(hidden_rows),
        "window_level_certificate_rows": len(window_rows),
        "first_target_tuple": first_tuple,
        "recommended_next_target_task": (
            "classify_hidden_output_normalization"
            if hidden_rows
            else "search_positive_reconstruction_criterion"
        ),
        "observability_boundary_status": "empirical_open_boundary_target_split_tooling",
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_target_split_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 50,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Expand observability atlas cases into per-target empirical readouts."""

    parsed_bases = _parse_bases(bases)
    atlas_rows = observability_atlas_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=top,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    atlas_case_rows = [
        row for row in atlas_rows if row.get("group") != OBSERVABILITY_SUMMARY_GROUP
    ]
    target_rows: list[dict[str, Any]] = []
    for row in atlas_case_rows:
        target_rows.extend(_observability_target_case_rows(row))
    return [
        _observability_target_split_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            atlas_case_rows=atlas_case_rows,
            target_rows=target_rows,
        ),
        *target_rows,
    ]


def _target_status(row: Mapping[str, Any], target_id: str) -> str:
    return str(row[f"{target_id}_observability_status"])


def _target_functional(row: Mapping[str, Any], target_id: str) -> bool | None:
    value = row.get(f"{target_id}_functional")
    if value is None:
        return None
    return bool(value)


def _first_nonfunctional_pointwise_target(row: Mapping[str, Any]) -> str | None:
    for target_id in (
        "raw_coefficient_nat",
        "coefficient_mod_block_base",
        "carried_block_value",
        "carry_state",
    ):
        if _target_functional(row, target_id) is False:
            return target_id
    return None


def _first_nonfunctional_pointwise_target_after_raw(
    row: Mapping[str, Any],
) -> str | None:
    for target_id in (
        "coefficient_mod_block_base",
        "carried_block_value",
        "carry_state",
    ):
        if _target_functional(row, target_id) is False:
            return target_id
    return None


def _observability_target_signature_family_class(row: Mapping[str, Any]) -> str:
    raw_obstructed = (
        _target_status(row, "raw_coefficient_nat") == "factor_through_obstructed"
    )
    mod_obstructed = (
        _target_status(row, "coefficient_mod_block_base")
        == "factor_through_obstructed"
    )
    carried_hidden = (
        _target_status(row, "carried_block_value")
        == "functional_output_hides_raw_coefficient_conflict"
    )
    carry_obstructed = (
        _target_status(row, "carry_state") == "factor_through_obstructed"
    )
    pointwise_functional = all(
        _target_functional(row, target_id) is True
        for target_id in (
            "raw_coefficient_nat",
            "coefficient_mod_block_base",
            "carried_block_value",
            "carry_state",
        )
    )
    if raw_obstructed and carried_hidden:
        return "raw_coefficient_obstructed_carried_output_hidden"
    if raw_obstructed and mod_obstructed:
        return "raw_and_mod_block_base_obstructed"
    if carry_obstructed and not raw_obstructed and not mod_obstructed:
        return "carry_state_first_loss"
    if pointwise_functional:
        return "all_pointwise_targets_functional_frontier"
    if row.get("coefficient_observability_class") == "gap_one_bridge_candidate":
        return "gap_one_bridge_signature"
    return "mixed_target_loss_frontier"


def _next_target_signature_task(family_class: str) -> str:
    if family_class == "raw_coefficient_obstructed_carried_output_hidden":
        return "classify_hidden_output_normalization_family"
    if family_class == "raw_and_mod_block_base_obstructed":
        return "compare_mod_block_base_information_loss_family"
    if family_class == "carry_state_first_loss":
        return "classify_remainder_to_carry_state_first_loss"
    if family_class == "all_pointwise_targets_functional_frontier":
        return "search_positive_coefficient_reconstruction_criterion"
    if family_class == "gap_one_bridge_signature":
        return "extend_gap_one_observability_bridge"
    return "inspect_mixed_target_loss_family"


def _tuple_from_observability_row(row: Mapping[str, Any]) -> list[int]:
    return [
        int(row["base"]),
        int(row["n"]),
        int(row["m"]),
        int(row["B"]),
        int(row["q"]),
        int(row["k"]),
        int(row["certified_lookahead_blocks"]),
        int(row["exact_gap_numerator"]),
    ]


def _observability_target_signature_family_row(
    *,
    signature_rank: int,
    signature: str,
    members: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    representative = members[0]
    family_class = _observability_target_signature_family_class(representative)
    member_tuples = [_tuple_from_observability_row(row) for row in members]
    member_keys = {(int(row["base"]), int(row["n"])) for row in members}
    n_values = sorted({int(row["n"]) for row in members})
    periodic_moduli = sorted({int(row["periodic_modulus"]) for row in members})
    k_values = sorted({int(row["k"]) for row in members})
    hidden_rows = [
        row
        for row in members
        if row.get("coefficient_observability_class") == "hidden_coefficient_conflict"
    ]
    functional_rows = [
        row
        for row in members
        if row.get("coefficient_observability_class")
        == "coefficient_functional_frontier"
    ]
    lean_ready_rows = [
        row
        for row in members
        if row.get("lean_readiness") == "existing_composite68_family_theorem"
    ]
    return {
        "group": OBSERVABILITY_TARGET_SIGNATURE_FAMILY_GROUP,
        "signature_rank": signature_rank,
        "observability_target_summary_signature": signature,
        "signature_family_class": family_class,
        "member_count": len(members),
        "bases": sorted({int(row["base"]) for row in members}),
        "n_value_count": len(n_values),
        "n_value_sample": n_values[:20],
        "periodic_modulus_count": len(periodic_moduli),
        "periodic_modulus_sample": periodic_moduli[:20],
        "k_value_count": len(k_values),
        "k_value_sample": k_values[:20],
        "min_n": n_values[0],
        "min_k": k_values[0],
        "member_tuple_sample": member_tuples[:12],
        "member_tuple_sample_size": min(len(member_tuples), 12),
        "representative_tuple": member_tuples[0],
        "contains_base10_68": (10, 68) in member_keys,
        "contains_base30_68": (30, 68) in member_keys,
        "contains_base10_97": (10, 97) in member_keys,
        "contains_base10_996": (10, 996) in member_keys,
        "min_exact_gap_numerator": min(int(row["exact_gap_numerator"]) for row in members),
        "min_certified_lookahead_blocks": min(
            int(row["certified_lookahead_blocks"]) for row in members
        ),
        "raw_coefficient_nat_status": _target_status(
            representative, "raw_coefficient_nat"
        ),
        "coefficient_mod_block_base_status": _target_status(
            representative, "coefficient_mod_block_base"
        ),
        "carried_block_value_status": _target_status(
            representative, "carried_block_value"
        ),
        "carry_state_status": _target_status(representative, "carry_state"),
        "remainder_state_status": _target_status(representative, "remainder_state"),
        "displayed_prefix_status": _target_status(representative, "displayed_prefix"),
        "raw_coefficient_nat_functional": _target_functional(
            representative, "raw_coefficient_nat"
        ),
        "coefficient_mod_block_base_functional": _target_functional(
            representative, "coefficient_mod_block_base"
        ),
        "carried_block_value_functional": _target_functional(
            representative, "carried_block_value"
        ),
        "carry_state_functional": _target_functional(representative, "carry_state"),
        "first_nonfunctional_pointwise_target": _first_nonfunctional_pointwise_target(
            representative
        ),
        "first_nonfunctional_pointwise_target_after_raw": (
            _first_nonfunctional_pointwise_target_after_raw(representative)
        ),
        "raw_coefficient_obstructed_cases": sum(
            1
            for row in members
            if _target_status(row, "raw_coefficient_nat")
            == "factor_through_obstructed"
        ),
        "coefficient_mod_block_base_loss_cases": sum(
            1
            for row in members
            if _target_status(row, "coefficient_mod_block_base")
            == "factor_through_obstructed"
        ),
        "carried_block_value_hidden_cases": sum(
            1
            for row in members
            if _target_status(row, "carried_block_value")
            == "functional_output_hides_raw_coefficient_conflict"
        ),
        "carried_block_value_functional_cases": sum(
            1
            for row in members
            if _target_functional(row, "carried_block_value") is True
        ),
        "carry_state_loss_cases": sum(
            1
            for row in members
            if _target_status(row, "carry_state") == "factor_through_obstructed"
        ),
        "hidden_coefficient_conflict_cases": len(hidden_rows),
        "functional_frontier_cases": len(functional_rows),
        "lean_ready_hidden_conflict_cases": len(lean_ready_rows),
        "target_signature_support_status": "empirical_open_boundary_signature_family",
        "next_target_signature_task": _next_target_signature_task(family_class),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def _observability_target_signature_sort_key(
    row: Mapping[str, Any],
) -> tuple[int, int, int, int, int, int]:
    return (
        OBSERVABILITY_TARGET_SIGNATURE_CLASS_ORDER[str(row["signature_family_class"])],
        -int(row["member_count"]),
        int(row["min_exact_gap_numerator"]),
        int(row["min_certified_lookahead_blocks"]),
        int(row["min_k"]),
        int(row["min_n"]),
    )


def _observability_target_signature_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_families: Sequence[dict[str, Any]],
    emitted_families: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    hidden_output_families = [
        row
        for row in all_families
        if row["signature_family_class"]
        == "raw_coefficient_obstructed_carried_output_hidden"
    ]
    mod_loss_families = [
        row
        for row in all_families
        if row["signature_family_class"] == "raw_and_mod_block_base_obstructed"
    ]
    carry_first_loss_families = [
        row
        for row in all_families
        if row["signature_family_class"] == "carry_state_first_loss"
    ]
    functional_families = [
        row
        for row in all_families
        if row["signature_family_class"] == "all_pointwise_targets_functional_frontier"
    ]
    if hidden_output_families:
        recommended = "classify_hidden_output_normalization_family"
    elif mod_loss_families:
        recommended = "compare_mod_block_base_information_loss_family"
    elif carry_first_loss_families:
        recommended = "classify_remainder_to_carry_state_first_loss"
    else:
        recommended = "search_positive_coefficient_reconstruction_criterion"
    return {
        "group": OBSERVABILITY_TARGET_SIGNATURE_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "total_signature_families": len(all_families),
        "emitted_signature_families": len(emitted_families),
        "hidden_output_signature_families": len(hidden_output_families),
        "mod_block_base_loss_signature_families": len(mod_loss_families),
        "carry_state_first_loss_signature_families": len(carry_first_loss_families),
        "functional_frontier_signature_families": len(functional_families),
        "first_hidden_output_signature": (
            hidden_output_families[0]["observability_target_summary_signature"]
            if hidden_output_families
            else None
        ),
        "recommended_next_target_signature_task": recommended,
        "observability_boundary_status": (
            "empirical_open_boundary_target_signature_tooling"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_target_signature_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Group atlas rows by their target-status signature."""

    parsed_bases = _parse_bases(bases)
    atlas_rows = observability_atlas_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    case_rows = [
        row for row in atlas_rows if row.get("group") != OBSERVABILITY_SUMMARY_GROUP
    ]
    by_signature: dict[str, list[dict[str, Any]]] = {}
    for row in case_rows:
        by_signature.setdefault(
            str(row["observability_target_summary_signature"]), []
        ).append(row)

    family_rows = [
        _observability_target_signature_family_row(
            signature_rank=0,
            signature=signature,
            members=sorted(members, key=_observability_sort_key),
        )
        for signature, members in by_signature.items()
    ]
    family_rows.sort(key=_observability_target_signature_sort_key)
    for rank, row in enumerate(family_rows, start=1):
        row["signature_rank"] = rank
    emitted_rows = list(family_rows[:top]) if top and top > 0 else list(family_rows)
    return [
        _observability_target_signature_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_families=family_rows,
            emitted_families=emitted_rows,
        ),
        *emitted_rows,
    ]


def _is_mod_stable_carry_loss_row(row: Mapping[str, Any]) -> bool:
    return (
        str(row.get("observability_target_summary_signature"))
        == MOD_STABLE_CARRY_LOSS_SIGNATURE
        and _target_status(row, "raw_coefficient_nat") == "factor_through_obstructed"
        and _target_status(row, "coefficient_mod_block_base")
        == "factor_through_candidate"
        and _target_status(row, "carried_block_value")
        == "functional_output_hides_raw_coefficient_conflict"
        and _target_status(row, "carry_state") == "factor_through_obstructed"
    )


def _mod_stable_carry_loss_sort_key(
    row: Mapping[str, Any],
) -> tuple[int, int, int, int, int]:
    return (
        int(row["exact_gap_numerator"]),
        int(row["certified_lookahead_blocks"]),
        int(row["k"]),
        int(row["n"]),
        int(row["base"]),
    )


def _mod_stable_carry_loss_case_row(
    row: Mapping[str, Any], rank: int
) -> dict[str, Any]:
    exported = dict(row)
    exported.update(
        {
            "group": OBSERVABILITY_MOD_STABLE_CARRY_LOSS_CASE_GROUP,
            "mod_stable_carry_loss_rank": rank,
            "target_signature_family_class": "mod_stable_carry_state_loss",
            "mod_stable_carry_loss_signature": MOD_STABLE_CARRY_LOSS_SIGNATURE,
            "coefficient_mod_block_base_preserved": True,
            "raw_coefficient_information_lost": True,
            "carried_output_hides_raw_conflict": True,
            "carry_state_information_lost": True,
            "first_nonfunctional_pointwise_target": "raw_coefficient_nat",
            "first_nonfunctional_pointwise_target_after_raw": "carry_state",
            "source_symmetry_signature": _source_symmetry_signature(
                _source_symmetry_key(row)
            ),
            "target_signature_support_status": (
                "empirical_open_boundary_mod_stable_carry_loss"
            ),
            "next_mod_stable_carry_loss_task": (
                "classify_carry_state_loss_after_mod_block_base_reduction"
            ),
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
        }
    )
    return exported


def _mod_stable_carry_loss_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_rows: Sequence[dict[str, Any]],
    emitted_rows: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    first_tuple = _tuple_from_observability_row(all_rows[0]) if all_rows else None
    source_signatures = sorted(
        {_source_symmetry_signature(_source_symmetry_key(row)) for row in all_rows}
    )
    return {
        "group": OBSERVABILITY_MOD_STABLE_CARRY_LOSS_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "total_mod_stable_carry_loss_cases": len(all_rows),
        "emitted_mod_stable_carry_loss_cases": len(emitted_rows),
        "bases_observed": sorted({int(row["base"]) for row in all_rows}),
        "source_symmetry_signature_count": len(source_signatures),
        "source_symmetry_signature_sample": source_signatures[:12],
        "first_mod_stable_carry_loss_tuple": first_tuple,
        "mod_stable_carry_loss_signature": MOD_STABLE_CARRY_LOSS_SIGNATURE,
        "recommended_next_mod_stable_carry_loss_task": (
            "classify_carry_state_loss_after_mod_block_base_reduction"
            if all_rows
            else "expand_observability_target_signature_scan"
        ),
        "observability_boundary_status": (
            "empirical_open_boundary_mod_stable_carry_loss_tooling"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_mod_stable_carry_loss_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Return rows for raw-loss/mod-stable/carry-loss hidden-output cases."""

    parsed_bases = _parse_bases(bases)
    atlas_rows = observability_atlas_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    matched_rows = sorted(
        (
            row
            for row in atlas_rows
            if row.get("group") != OBSERVABILITY_SUMMARY_GROUP
            and _is_mod_stable_carry_loss_row(row)
        ),
        key=_mod_stable_carry_loss_sort_key,
    )
    emitted_base_rows = (
        list(matched_rows[:top]) if top and top > 0 else list(matched_rows)
    )
    emitted_rows = [
        _mod_stable_carry_loss_case_row(row, rank)
        for rank, row in enumerate(emitted_base_rows, start=1)
    ]
    return [
        _mod_stable_carry_loss_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_rows=matched_rows,
            emitted_rows=emitted_rows,
        ),
        *emitted_rows,
    ]


def _shape13_k4_family_role(row: Mapping[str, Any]) -> str:
    periodic_modulus = int(row["periodic_modulus"])
    denominator = int(row["n"])
    if denominator == periodic_modulus:
        return "source_core_reference"
    if denominator % periodic_modulus == 0:
        return "base_supported_shift_member"
    return "finite_mod_stable_carry_loss_member"


def _shape13_k4_family_note(row: Mapping[str, Any]) -> str:
    role = _shape13_k4_family_role(row)
    if role == "source_core_reference":
        return "N=13 is the base-30 source-core reference with conflict window [0,6]"
    if role == "base_supported_shift_member":
        return "N=26 is the first shifted base-30 member with conflict window [1,7]"
    return "same source shape under the mod-stable carry-loss target profile"


def _shape13_k4_member_sort_key(row: Mapping[str, Any]) -> tuple[int, int, int, int]:
    role_order = {
        "source_core_reference": 0,
        "base_supported_shift_member": 1,
        "finite_mod_stable_carry_loss_member": 2,
    }
    role = _shape13_k4_family_role(row)
    positions = list(row.get("conflict_positions") or [])
    first_position = int(positions[0]) if positions else 999999
    return (
        role_order.get(role, 99),
        int(row["base"]),
        int(row["n"]),
        first_position,
    )


def _shape13_k4_next_task(
    *,
    proved_cases: int,
    candidate_cases: int,
    finite_only_cases: int,
) -> str:
    if candidate_cases:
        return "add_named_shape13_k4_shift_instantiation_for_candidate_rows"
    if finite_only_cases:
        return "add_finite_shape13_k4_package_or_reject_extra_member"
    if proved_cases:
        return "mine_wider_shape13_k4_members_or_generalize_scale_two_criterion"
    return "expand_shape13_k4_mod_stable_carry_loss_scan"


def _shape13_k4_raw_coefficient(row: Mapping[str, Any], position: int) -> int:
    return int(row["q"]) * int(row["k"]) ** position


def _shape13_k4_scale_two_hypothesis_fields(
    row: Mapping[str, Any],
    *,
    core_row: Mapping[str, Any] | None,
) -> dict[str, Any]:
    periodic_modulus = int(row["periodic_modulus"])
    denominator = int(row["n"])
    multiplier = (
        denominator // periodic_modulus
        if denominator % periodic_modulus == 0
        else None
    )
    block_base = int(row["B"])
    remainder_k = int(row["k"])
    quotient_gap = block_base - remainder_k
    source_positions = (
        [int(position) for position in core_row.get("conflict_positions", [])]
        if core_row is not None
        else []
    )
    source_block_values = (
        [int(value) for value in core_row.get("conflict_block_values", [])]
        if core_row is not None
        else []
    )
    source_block_base = int(core_row["B"]) if core_row is not None else None

    good_mode = block_base > denominator and int(row["q"]) > 0
    same_core_compatible = (
        multiplier is not None
        and int(row["preperiod_digits"]) <= int(row["m"])
        and remainder_k < periodic_modulus
    )
    factor_times_two_eq_k = (
        multiplier * 2 == remainder_k if multiplier is not None else False
    )

    def quotient_remainder_bound(position_index: int) -> bool | None:
        if core_row is None or len(source_positions) <= position_index or quotient_gap <= 0:
            return None
        raw = _shape13_k4_raw_coefficient(
            core_row, source_positions[position_index] + 1
        )
        return 2 * (raw % quotient_gap) < quotient_gap

    def block_remainder_bound(position_index: int) -> bool | None:
        if (
            source_block_base is None
            or len(source_block_values) <= position_index
            or source_block_base <= 0
        ):
            return None
        return 2 * source_block_values[position_index] < source_block_base

    left_quotient_remainder_bound = quotient_remainder_bound(0)
    right_quotient_remainder_bound = quotient_remainder_bound(1)
    quotient_remainder_bounds = (
        left_quotient_remainder_bound is True
        and right_quotient_remainder_bound is True
    )
    left_block_remainder_bound = block_remainder_bound(0)
    right_block_remainder_bound = block_remainder_bound(1)
    block_remainder_bounds = (
        left_block_remainder_bound is True and right_block_remainder_bound is True
    )
    source_core_hidden_output = (
        len(source_block_values) >= 2 and source_block_values[0] == source_block_values[1]
    )

    checks = [
        ("not_good_mode", good_mode),
        ("not_same_core_compatible", same_core_compatible),
        ("base_prime_support_times_two_ne_k", factor_times_two_eq_k),
        ("left_scaled_quotient_remainder_bound_failed", left_quotient_remainder_bound),
        ("right_scaled_quotient_remainder_bound_failed", right_quotient_remainder_bound),
        ("left_scaled_block_remainder_bound_failed", left_block_remainder_bound),
        ("right_scaled_block_remainder_bound_failed", right_block_remainder_bound),
        ("source_core_hidden_carry_block_value_missing", source_core_hidden_output),
    ]
    failures = [reason for reason, value in checks if value is not True]
    hypotheses_hold = not failures

    return {
        "shape13_k4_hyp_good_mode": good_mode,
        "shape13_k4_hyp_same_core_compatible": same_core_compatible,
        "shape13_k4_hyp_base_prime_support_times_two_eq_k": (
            factor_times_two_eq_k
        ),
        "shape13_k4_hyp_left_scaled_quotient_remainder_lt_gap": (
            left_quotient_remainder_bound
        ),
        "shape13_k4_hyp_right_scaled_quotient_remainder_lt_gap": (
            right_quotient_remainder_bound
        ),
        "shape13_k4_hyp_scaled_quotient_remainders_lt_gap": (
            quotient_remainder_bounds
        ),
        "shape13_k4_hyp_left_scaled_block_remainder_lt_block_base": (
            left_block_remainder_bound
        ),
        "shape13_k4_hyp_right_scaled_block_remainder_lt_block_base": (
            right_block_remainder_bound
        ),
        "shape13_k4_hyp_scaled_block_remainders_lt_block_base": (
            block_remainder_bounds
        ),
        "shape13_k4_hyp_source_core_hidden_carry_block_value": (
            source_core_hidden_output
        ),
        "shape13_k4_scale_two_hypotheses_hold": hypotheses_hold,
        "shape13_k4_scale_two_failure_reason": (
            None if hypotheses_hold else "|".join(failures)
        ),
    }


def _shape13_k4_member_fields(
    row: Mapping[str, Any],
    *,
    core_row: Mapping[str, Any] | None,
) -> dict[str, Any]:
    periodic_modulus = int(row["periodic_modulus"])
    denominator = int(row["n"])
    multiplier = (
        denominator // periodic_modulus
        if denominator % periodic_modulus == 0
        else None
    )
    positions = [int(position) for position in row.get("conflict_positions") or []]
    core_positions = (
        [int(position) for position in core_row.get("conflict_positions", [])]
        if core_row is not None
        else None
    )
    position_shift = (
        positions[0] - core_positions[0]
        if positions and core_positions
        else None
    )
    preperiod_shift = (
        int(row["preperiod_digits"]) - int(core_row["preperiod_digits"])
        if core_row is not None
        else None
    )
    core_q = int(core_row["q"]) if core_row is not None else None
    quotient_scales_to_core = (
        int(row["q"]) * multiplier == core_q
        if multiplier is not None and core_q is not None
        else None
    )
    role = _shape13_k4_family_role(row)
    named_instantiation = SHAPE13_K4_NAMED_SHIFT_INSTANTIATIONS.get(
        (int(row["base"]), denominator)
    )
    shift_hypotheses_hold = (
        role == "base_supported_shift_member"
        and position_shift == 1
        and preperiod_shift == 1
        and quotient_scales_to_core is True
    )
    scale_two_fields = _shape13_k4_scale_two_hypothesis_fields(
        row, core_row=core_row
    )
    scale_two_hypotheses_hold = bool(
        scale_two_fields["shape13_k4_scale_two_hypotheses_hold"]
    )
    if role == "source_core_reference":
        support_status = "source_core_reference"
        proof_surface = "finite_source_core_reference"
        failure_reason = None
    elif (
        shift_hypotheses_hold
        and scale_two_hypotheses_hold
        and named_instantiation is not None
    ):
        support_status = "mod_stable_carry_loss_shift_proved_by_arithmetic_criterion"
        proof_surface = "lean_named_arithmetic_criterion"
        failure_reason = None
    elif shift_hypotheses_hold and scale_two_hypotheses_hold:
        support_status = "mod_stable_carry_loss_shift_candidate"
        proof_surface = "exported_mod_stable_shift_hypotheses"
        failure_reason = "no_named_lean_instantiation"
    else:
        support_status = "finite_only_mod_stable_carry_loss"
        proof_surface = "finite_conflict_record_only"
        failure_reasons = []
        if not shift_hypotheses_hold:
            failure_reasons.append("shape13_shift_hypotheses_not_satisfied")
        if scale_two_fields["shape13_k4_scale_two_failure_reason"] is not None:
            failure_reasons.append(
                scale_two_fields["shape13_k4_scale_two_failure_reason"]
            )
        failure_reason = "|".join(failure_reasons)

    return {
        "source_symmetry_family_role": role,
        "shape13_k4_family_role": role,
        "shape13_k4_family_note": _shape13_k4_family_note(row),
        "shape13_k4_support_status": support_status,
        "shape13_k4_proof_surface": proof_surface,
        "shape13_k4_failure_reason": failure_reason,
        "shape13_k4_source_core_n": periodic_modulus,
        "shape13_k4_periodic_modulus": periodic_modulus,
        "shape13_k4_remainder_k": int(row["k"]),
        "shape13_k4_position_gap": int(row["conflict_position_gap"]),
        "shape13_k4_source_positions": core_positions,
        "shape13_k4_target_positions": positions,
        "shape13_k4_position_shift_from_core": position_shift,
        "shape13_k4_preperiod_shift_from_core": preperiod_shift,
        "shape13_k4_denominator_multiplier_from_core": multiplier,
        "shape13_k4_core_q": core_q,
        "shape13_k4_q_times_denominator_multiplier_eq_core_q": (
            quotient_scales_to_core
        ),
        "shape13_k4_same_periodic_core": denominator % periodic_modulus == 0,
        "shape13_k4_shift_criterion_theorem": (
            SHAPE13_K4_SCALE_TWO_CRITERION_THEOREM
            if shift_hypotheses_hold
            else None
        ),
        "shape13_k4_named_instantiation": named_instantiation,
        "shape13_k4_coefficient_mod_block_base_preserved": bool(
            row.get("coefficient_mod_block_base_preserved")
        ),
        "shape13_k4_carried_output_hides_raw_conflict": bool(
            row.get("carried_output_hides_raw_conflict")
        ),
        "shape13_k4_carry_state_information_lost": bool(
            row.get("carry_state_information_lost")
        ),
        **scale_two_fields,
        "shape13_k4_next_lean_task": (
            "generalize_shape13_scale_two_criterion_beyond_base30_13_26"
            if support_status
            == "mod_stable_carry_loss_shift_proved_by_arithmetic_criterion"
            else "prove_or_reject_shape13_k4_mod_stable_carry_loss_shift"
        ),
    }


def _shape13_k4_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_members: Sequence[dict[str, Any]],
    emitted_members: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    source_core = next(
        (
            row
            for row in all_members
            if row["shape13_k4_family_role"] == "source_core_reference"
        ),
        None,
    )
    shifted_member = next(
        (
            row
            for row in all_members
            if row["shape13_k4_family_role"] == "base_supported_shift_member"
        ),
        None,
    )
    proved_cases = sum(
        1
        for row in all_members
        if row["shape13_k4_support_status"]
        == "mod_stable_carry_loss_shift_proved_by_arithmetic_criterion"
    )
    candidate_cases = sum(
        1
        for row in all_members
        if row["shape13_k4_support_status"]
        == "mod_stable_carry_loss_shift_candidate"
    )
    finite_only_cases = sum(
        1
        for row in all_members
        if row["shape13_k4_support_status"]
        == "finite_only_mod_stable_carry_loss"
    )
    scale_two_ready_cases = sum(
        1
        for row in all_members
        if row["shape13_k4_scale_two_hypotheses_hold"] is True
    )
    scale_two_failed_cases = sum(
        1
        for row in all_members
        if row["shape13_k4_scale_two_hypotheses_hold"] is not True
    )
    scale_two_unnamed_candidates = [
        row
        for row in all_members
        if row["shape13_k4_scale_two_hypotheses_hold"] is True
        and row["shape13_k4_named_instantiation"] is None
        and row["shape13_k4_family_role"] != "source_core_reference"
    ]
    only_base30_pair = (
        sorted({int(row["n"]) for row in all_members}) == [13, 26]
        and sorted({int(row["base"]) for row in all_members}) == [30]
    )
    next_task = _shape13_k4_next_task(
        proved_cases=proved_cases,
        candidate_cases=candidate_cases,
        finite_only_cases=finite_only_cases,
    )
    return {
        "group": OBSERVABILITY_SHAPE13_K4_MOD_STABLE_CARRY_LOSS_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "source_symmetry_signature": SHAPE13_K4_MOD_STABLE_SOURCE_SYMMETRY_SIGNATURE,
        "family_class": "shape13_k4_mod_stable_carry_loss_shift",
        "total_members": len(all_members),
        "emitted_members": len(emitted_members),
        "n_values": sorted({int(row["n"]) for row in all_members}),
        "bases_observed": sorted({int(row["base"]) for row in all_members}),
        "source_core_present": source_core is not None,
        "base30_n26_shift_present": any(
            int(row["base"]) == 30 and int(row["n"]) == 26
            for row in all_members
        ),
        "source_core_tuple": (
            _tuple_from_observability_row(source_core)
            if source_core is not None
            else None
        ),
        "shifted_member_tuple": (
            _tuple_from_observability_row(shifted_member)
            if shifted_member is not None
            else None
        ),
        "observed_position_windows": sorted(
            {
                "[" + ",".join(str(position) for position in row["conflict_positions"]) + "]"
                for row in all_members
            }
        ),
        "mod_stable_shift_proved_cases": proved_cases,
        "mod_stable_shift_candidate_cases": candidate_cases,
        "finite_only_mod_stable_carry_loss_cases": finite_only_cases,
        "shape13_k4_scale_two_hypothesis_ready_members": scale_two_ready_cases,
        "shape13_k4_scale_two_hypothesis_failed_members": scale_two_failed_cases,
        "shape13_k4_scale_two_unnamed_candidate_members": len(
            scale_two_unnamed_candidates
        ),
        "shape13_k4_scale_two_unnamed_candidate_tuples": [
            _tuple_from_observability_row(row) for row in scale_two_unnamed_candidates
        ],
        "shape13_k4_scale_two_candidate_mining_status": (
            "unnamed_scale_two_ready_members_require_named_lean_instantiation"
            if scale_two_unnamed_candidates
            else "no_unnamed_scale_two_ready_members_under_current_bounds"
        ),
        "shape13_k4_current_scan_status": (
            "only_base30_core_and_shift_pair_under_current_bounds"
            if only_base30_pair
            else "additional_shape13_k4_members_observed_under_current_bounds"
        ),
        "shape13_k4_current_scan_stop_condition": (
            "do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member"
            if only_base30_pair and candidate_cases == 0 and finite_only_cases == 0
            else "classify_new_shape13_k4_members_by_named_criterion_or_finite_package"
        ),
        "shape13_k4_wider_probe_note": (
            "manual probe found no additional members for bases 7,10,12,30 through max_n=2000 "
            "or for bases 7,10,12,30,32,64,66,72,98,100 through max_n=1200"
        ),
        "shape13_k4_wider_scale_two_candidate_probe_note": (
            "manual scale-two candidate probe found no unnamed scale-two-ready members for "
            "bases 7,10,12,30 through max_n=2000 or for bases "
            "7,10,12,30,32,64,66,72,98,100 through max_n=1200"
        ),
        "all_members_coefficient_mod_block_base_preserved": all(
            bool(row["shape13_k4_coefficient_mod_block_base_preserved"])
            for row in all_members
        ),
        "all_members_carried_output_hides_raw_conflict": all(
            bool(row["shape13_k4_carried_output_hides_raw_conflict"])
            for row in all_members
        ),
        "all_members_carry_state_information_lost": all(
            bool(row["shape13_k4_carry_state_information_lost"])
            for row in all_members
        ),
        "observability_boundary_status": (
            "empirical_open_boundary_shape13_k4_mod_stable_carry_loss_classifier"
        ),
        "recommended_next_observability_task": next_task,
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_shape13_k4_mod_stable_carry_loss_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Classify the first mod-stable carry-loss source-shape family."""

    parsed_bases = _parse_bases(bases)
    mod_stable_rows = observability_mod_stable_carry_loss_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    base_members = [
        row
        for row in mod_stable_rows
        if row.get("group") == OBSERVABILITY_MOD_STABLE_CARRY_LOSS_CASE_GROUP
        and row.get("source_symmetry_signature")
        == SHAPE13_K4_MOD_STABLE_SOURCE_SYMMETRY_SIGNATURE
    ]
    core_row = next(
        (
            row
            for row in base_members
            if int(row["n"]) == int(row["periodic_modulus"])
        ),
        None,
    )
    classified_members: list[dict[str, Any]] = []
    for row in sorted(base_members, key=_shape13_k4_member_sort_key):
        shape13_fields = _shape13_k4_member_fields(row, core_row=core_row)
        exported = dict(row)
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE13_K4_MOD_STABLE_CARRY_LOSS_MEMBER_GROUP,
                "family_class": "shape13_k4_mod_stable_carry_loss_shift",
                "observability_boundary_status": (
                    "empirical_open_boundary_shape13_k4_mod_stable_carry_loss_classifier"
                ),
                "next_observability_task": shape13_fields["shape13_k4_next_lean_task"],
                **shape13_fields,
            }
        )
        classified_members.append(exported)

    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank

    emitted_members = (
        classified_members[:top] if top and top > 0 else list(classified_members)
    )
    return [
        _shape13_k4_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _source_symmetry_key(row: Mapping[str, Any]) -> tuple[int, int, int]:
    return (
        int(row["periodic_modulus"]),
        int(row["k"]),
        int(row["conflict_position_gap"]),
    )


def _source_symmetry_signature(key: tuple[int, int, int]) -> str:
    periodic_modulus, remainder_k, position_gap = key
    return (
        f"periodic_modulus={periodic_modulus};k={remainder_k};"
        f"position_gap={position_gap}"
    )


def _instrument_observation_status(row: Mapping[str, Any]) -> str:
    if row["coefficient_observability_class"] == "visible_coefficient_conflict":
        return "reveals_source_symmetry"
    if bool(row.get("carry_output_hides_conflict")):
        return "hides_source_symmetry"
    return "exposes_coefficient_conflict"


def _source_position_signature(row: Mapping[str, Any]) -> str:
    positions = ",".join(str(position) for position in row["conflict_positions"])
    return f"positions=[{positions}]"


def _source_shape_sort_key(shape: Mapping[str, Any]) -> tuple[int, int, int, int, int, int]:
    return (
        -int(shape["lean_ready_member_count"]),
        -int(shape["base_count"]),
        -int(shape["member_count"]),
        int(shape["min_exact_gap_numerator"]),
        int(shape["min_certified_lookahead_blocks"]),
        int(shape["periodic_modulus"]),
    )


def _source_shape_row(
    *,
    key: tuple[int, int, int],
    members: Sequence[dict[str, Any]],
    rank: int,
) -> dict[str, Any]:
    signature = _source_symmetry_signature(key)
    canonical_positions = list(members[0]["conflict_positions"])
    hidden_members = [
        row
        for row in members
        if row["coefficient_observability_class"] == "hidden_coefficient_conflict"
    ]
    visible_members = [
        row
        for row in members
        if row["coefficient_observability_class"] == "visible_coefficient_conflict"
    ]
    shifted_members = [
        row for row in members if list(row["conflict_positions"]) != canonical_positions
    ]
    bases_observed = sorted({int(row["base"]) for row in members})
    hidden_bases = sorted({int(row["base"]) for row in hidden_members})
    visible_bases = sorted({int(row["base"]) for row in visible_members})
    shifted_bases = sorted({int(row["base"]) for row in shifted_members})
    exact_position_signatures = sorted(
        {_source_position_signature(row) for row in members}
    )
    observation_summary = sorted(
        {
            f"base{int(row['base'])}:{_instrument_observation_status(row)}:"
            f"{'shifted_position_window' if row in shifted_members else 'same_position_window'}"
            for row in members
        }
    )
    periodic_modulus, remainder_k, position_gap = key
    remainder_states = sorted({int(row["conflict_remainder_state"]) for row in members})
    return {
        "group": OBSERVABILITY_SOURCE_SHAPE_GROUP,
        "shape_rank": rank,
        "source_symmetry_signature": signature,
        "periodic_modulus": periodic_modulus,
        "k": remainder_k,
        "canonical_conflict_remainder_state": int(members[0]["conflict_remainder_state"]),
        "conflict_remainder_states": remainder_states,
        "conflict_position_gap": position_gap,
        "canonical_conflict_positions": canonical_positions,
        "exact_position_signatures": exact_position_signatures,
        "member_count": len(members),
        "base_count": len(bases_observed),
        "bases_observed": bases_observed,
        "hidden_bases": hidden_bases,
        "visible_bases": visible_bases,
        "shifted_bases": shifted_bases,
        "source_symmetry_shift_observed": bool(shifted_members),
        "lean_ready_member_count": sum(
            1
            for row in members
            if row["lean_readiness"] == "existing_composite68_family_theorem"
        ),
        "min_certified_lookahead_blocks": min(
            int(row["certified_lookahead_blocks"]) for row in members
        ),
        "min_exact_gap_numerator": min(
            int(row["exact_gap_numerator"]) for row in members
        ),
        "coefficient_information_lost": bool(hidden_members),
        "carry_output_hides_conflict": bool(hidden_members),
        "instrument_observation_summary": observation_summary,
        "observability_boundary_status": "empirical_open_boundary_instrument_comparison",
        "next_observability_task": (
            "classify_cross_base_hidden_source_symmetry"
            if hidden_members
            else "compare_visible_source_symmetry_instruments"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def _source_shape_member_rows(
    *,
    shape_row: Mapping[str, Any],
    members: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    canonical_positions = list(shape_row["canonical_conflict_positions"])
    member_rows: list[dict[str, Any]] = []
    for member_rank, row in enumerate(members, start=1):
        exported = dict(row)
        shifted = list(row["conflict_positions"]) != canonical_positions
        exported.update(
            {
                "group": OBSERVABILITY_INSTRUMENT_MEMBER_GROUP,
                "shape_rank": shape_row["shape_rank"],
                "member_rank": member_rank,
                "source_symmetry_signature": shape_row["source_symmetry_signature"],
                "instrument_observation_status": _instrument_observation_status(row),
                "source_symmetry_shift_status": (
                    "shifted_position_window" if shifted else "same_position_window"
                ),
                "canonical_conflict_positions": canonical_positions,
            }
        )
        member_rows.append(exported)
    return member_rows


def _observability_instrument_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_shapes: Sequence[dict[str, Any]],
    emitted_shapes: Sequence[dict[str, Any]],
    emitted_member_count: int,
) -> dict[str, Any]:
    cross_base_shapes = [shape for shape in all_shapes if int(shape["base_count"]) > 1]
    shifted_shapes = [
        shape for shape in all_shapes if bool(shape["source_symmetry_shift_observed"])
    ]
    visible_shapes = [shape for shape in all_shapes if shape["visible_bases"]]
    first_signature = (
        str(emitted_shapes[0]["source_symmetry_signature"]) if emitted_shapes else None
    )
    return {
        "group": OBSERVABILITY_INSTRUMENT_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "total_shapes": len(all_shapes),
        "emitted_shapes": len(emitted_shapes),
        "emitted_members": emitted_member_count,
        "cross_base_shape_count": len(cross_base_shapes),
        "shifted_shape_count": len(shifted_shapes),
        "visible_shape_count": len(visible_shapes),
        "first_source_symmetry_signature": first_signature,
        "observability_boundary_status": "empirical_open_boundary_instrument_comparison",
        "recommended_next_observability_task": (
            "classify_cross_base_hidden_source_symmetry"
            if cross_base_shapes
            else "expand_observability_instrument_search"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_instrument_comparison_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Group observability rows by source symmetry and compare base instruments."""

    parsed_bases = _parse_bases(bases)
    atlas_rows = observability_atlas_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    conflict_rows = [
        row
        for row in atlas_rows
        if row.get("coefficient_observability_class")
        in {"hidden_coefficient_conflict", "visible_coefficient_conflict"}
    ]
    hidden_keys = {
        _source_symmetry_key(row)
        for row in conflict_rows
        if row["coefficient_observability_class"] == "hidden_coefficient_conflict"
    }
    grouped: dict[tuple[int, int, int], list[dict[str, Any]]] = {
        key: [] for key in hidden_keys
    }
    for row in conflict_rows:
        key = _source_symmetry_key(row)
        if key in grouped:
            grouped[key].append(row)

    shape_pairs: list[tuple[dict[str, Any], list[dict[str, Any]]]] = []
    for key, members in grouped.items():
        members.sort(key=_observability_sort_key)
        shape_pairs.append(
            (
                _source_shape_row(key=key, members=members, rank=0),
                members,
            )
        )
    shape_pairs.sort(key=lambda pair: _source_shape_sort_key(pair[0]))
    if top and top > 0:
        shape_pairs = shape_pairs[:top]
    for rank, (shape, _) in enumerate(shape_pairs, start=1):
        shape["shape_rank"] = rank

    emitted_rows: list[dict[str, Any]] = []
    emitted_member_count = 0
    for shape, members in shape_pairs:
        emitted_rows.append(shape)
        member_rows = _source_shape_member_rows(shape_row=shape, members=members)
        emitted_member_count += len(member_rows)
        emitted_rows.extend(member_rows)

    all_shape_rows = [
        _source_shape_row(key=key, members=members, rank=0)
        for key, members in grouped.items()
    ]
    return [
        _observability_instrument_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_shapes=all_shape_rows,
            emitted_shapes=[shape for shape, _ in shape_pairs],
            emitted_member_count=emitted_member_count,
        ),
        *emitted_rows,
    ]


def _shape17_family_role(row: Mapping[str, Any]) -> str:
    same_core_multiplier = int(row["n"]) // 17 if int(row["n"]) % 17 == 0 else 0
    if same_core_multiplier == 1:
        return "periodic_core_shifted_member"
    if same_core_multiplier == 2:
        return "double_core_composite_style_member"
    if same_core_multiplier == 4:
        return "composite68_style_member"
    return "same_core_scaled_member"


def _shape17_family_bridge_note(row: Mapping[str, Any]) -> str:
    role = _shape17_family_role(row)
    if role == "periodic_core_shifted_member":
        return "N=17 carries the same source shape in the shifted [0,4] window"
    if role == "double_core_composite_style_member":
        return "N=34 keeps the same source shape in the Composite68-style [1,5] window"
    if role == "composite68_style_member":
        return "N=68 is the Composite68-style member; base 10 and 30 rows are Lean-ready anchors"
    return "same periodic core with the first source shape under a larger multiplier"


def _base_local_coefficient_scales(
    members: Sequence[Mapping[str, Any]]
) -> dict[int, int]:
    minima: dict[int, int] = {}
    for row in members:
        coefficients = list(row.get("conflict_coefficients") or [])
        if not coefficients:
            continue
        base = int(row["base"])
        first_coefficient = int(coefficients[0])
        minima[base] = min(minima.get(base, first_coefficient), first_coefficient)
    return minima


def _shape17_same_core_shift_hypotheses(
    row: Mapping[str, Any],
    *,
    same_core_multiplier: int | None,
    local_scale: int | None,
    source_positions: Sequence[int],
) -> tuple[bool | None, bool | None, bool | None]:
    if same_core_multiplier is None or local_scale is None:
        return None, None, None
    block_base = int(row["B"])
    remainder_k = int(row["k"])
    gap = block_base - remainder_k
    if gap <= 0:
        return None, None, None
    core_q = int(row["q"]) * same_core_multiplier
    support_times_scale = same_core_multiplier * local_scale == remainder_k
    quotient_remainders_fit = all(
        local_scale * ((core_q * (remainder_k ** (position + 1))) % gap) < gap
        for position in source_positions
    )
    block_remainders_fit = all(
        local_scale
        * (
            (
                core_q * (remainder_k**position)
                + (core_q * (remainder_k ** (position + 1))) // gap
            )
            % block_base
        )
        < block_base
        for position in source_positions
    )
    return support_times_scale, quotient_remainders_fit, block_remainders_fit


def _shape17_same_core_shift_fields(
    row: Mapping[str, Any],
    *,
    same_core_multiplier: int | None,
    local_scale: int | None,
) -> dict[str, Any]:
    role = _shape17_family_role(row)
    positions = list(row.get("conflict_positions") or [])
    if role == "periodic_core_shifted_member":
        return {
            "same_core_shift_support_status": "source_core_reference",
            "same_core_shift_proof_surface": "finite_source_core_reference",
            "same_core_shift_scale": local_scale,
            "same_core_shift_source_positions": positions,
            "same_core_shift_target_positions": [position + 1 for position in positions],
            "same_core_hyp_base_prime_support_times_scale_eq_k": None,
            "same_core_hyp_scaled_quotient_remainder_lt_gap": None,
            "same_core_hyp_scaled_block_remainder_lt_block_base": None,
            "same_core_shift_criterion_theorem": None,
            "same_core_shift_named_instantiation": None,
            "same_core_shift_failure_reason": None,
        }
    if not positions or min(positions) == 0:
        fields = _same_core_shift_default_fields(row)
        fields["same_core_shift_failure_reason"] = "no_one_block_source_window"
        return fields

    source_positions = [position - 1 for position in positions]
    support_times_scale, quotient_fit, block_fit = _shape17_same_core_shift_hypotheses(
        row,
        same_core_multiplier=same_core_multiplier,
        local_scale=local_scale,
        source_positions=source_positions,
    )
    hypotheses_hold = all(
        value is True for value in (support_times_scale, quotient_fit, block_fit)
    )
    named_instantiation = SHAPE17_K4_NAMED_SHIFT_INSTANTIATIONS.get(
        (int(row["base"]), int(row["n"]))
    )
    if hypotheses_hold and named_instantiation is not None:
        status = "same_core_shift_proved_by_arithmetic_criterion"
        proof_surface = "lean_named_arithmetic_criterion"
        failure_reason = None
    elif hypotheses_hold:
        status = "same_core_shift_criterion_candidate"
        proof_surface = "exported_arithmetic_hypotheses"
        failure_reason = "no_named_lean_instantiation"
    else:
        status = "finite_only_hidden_conflict"
        proof_surface = "finite_conflict_record_only"
        failure_reason = "same_core_shift_hypotheses_not_satisfied"

    return {
        "same_core_shift_support_status": status,
        "same_core_shift_proof_surface": proof_surface,
        "same_core_shift_scale": local_scale,
        "same_core_shift_source_positions": source_positions,
        "same_core_shift_target_positions": positions,
        "same_core_hyp_base_prime_support_times_scale_eq_k": support_times_scale,
        "same_core_hyp_scaled_quotient_remainder_lt_gap": quotient_fit,
        "same_core_hyp_scaled_block_remainder_lt_block_base": block_fit,
        "same_core_shift_criterion_theorem": (
            SAME_CORE_SHIFT_GENERIC_CRITERION_THEOREM if hypotheses_hold else None
        ),
        "same_core_shift_named_instantiation": named_instantiation,
        "same_core_shift_failure_reason": failure_reason,
    }


def _shape17_member_sort_key(row: Mapping[str, Any]) -> tuple[int, int, int, int]:
    same_core_multiplier = int(row["n"]) // 17 if int(row["n"]) % 17 == 0 else 999
    positions = list(row.get("conflict_positions") or [])
    first_position = int(positions[0]) if positions else 999
    return (
        same_core_multiplier,
        first_position,
        int(row["n"]),
        int(row["base"]),
    )


def _shape17_family_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_members: Sequence[dict[str, Any]],
    emitted_members: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    multipliers = sorted(
        {
            int(row["same_core_multiplier"])
            for row in all_members
            if row.get("same_core_multiplier") is not None
        }
    )
    n_values = sorted({int(row["n"]) for row in all_members})
    return {
        "group": OBSERVABILITY_SHAPE17_K4_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "source_symmetry_signature": SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE,
        "family_class": "first_emitted_shape17_k4_position_gap_four",
        "total_members": len(all_members),
        "emitted_members": len(emitted_members),
        "n_values": n_values,
        "same_core_multipliers": multipliers,
        "shifted_member_count": sum(
            1
            for row in all_members
            if row["source_symmetry_shift_status"] == "shifted_position_window"
        ),
        "composite68_style_member_count": sum(
            1
            for row in all_members
            if row["source_symmetry_family_role"] == "composite68_style_member"
        ),
        "lean_ready_member_count": sum(
            1
            for row in all_members
            if row["lean_readiness"] == "existing_composite68_family_theorem"
        ),
        "same_core_shift_proved_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"]
            == "same_core_shift_proved_by_arithmetic_criterion"
        ),
        "same_core_shift_candidate_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"] == "same_core_shift_criterion_candidate"
        ),
        "finite_only_hidden_conflict_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"] == "finite_only_hidden_conflict"
        ),
        "observability_boundary_status": (
            "empirical_open_boundary_shape17_k4_family_classifier"
        ),
        "recommended_next_observability_task": (
            "prove_or_reject_shape17_same_core_shift_pattern"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_shape17_k4_family_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Classify the first emitted observability source-shape family."""

    parsed_bases = _parse_bases(bases)
    comparison_rows = observability_instrument_comparison_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    members = [
        row
        for row in comparison_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature")
        == SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    for row in members:
        exported = dict(row)
        same_core_multiplier = (
            int(row["n"]) // 17 if int(row["n"]) % 17 == 0 else None
        )
        positions = list(row.get("conflict_positions") or [])
        canonical_positions = list(row.get("canonical_conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE17_K4_MEMBER_GROUP,
                "family_class": "first_emitted_shape17_k4_position_gap_four",
                "source_symmetry_family_role": _shape17_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "shape17_family_bridge_note": _shape17_family_bridge_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_shape17_k4_family_classifier"
                ),
                "next_observability_task": (
                    "prove_or_reject_shape17_same_core_shift_pattern"
                ),
                **_shape17_same_core_shift_fields(
                    row,
                    same_core_multiplier=same_core_multiplier,
                    local_scale=local_scale,
                ),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_shape17_member_sort_key)
    if top and top > 0:
        emitted_members = classified_members[:top]
    else:
        emitted_members = classified_members
    return [
        _shape17_family_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _generic_source_shape_family_role(row: Mapping[str, Any]) -> str:
    if row.get("source_symmetry_shift_status") == "shifted_position_window":
        return "shifted_position_member"
    periodic_modulus = int(row["periodic_modulus"])
    denominator = int(row["n"])
    if denominator % periodic_modulus != 0:
        return "same_position_nonmultiple_member"
    multiplier = denominator // periodic_modulus
    if multiplier == 1:
        return "source_core_reference"
    return "same_position_scaled_member"


def _generic_source_shape_family_note(row: Mapping[str, Any]) -> str:
    role = _generic_source_shape_family_role(row)
    if role == "shifted_position_member":
        return "same source shape appears in a shifted finite window"
    if role == "source_core_reference":
        return "periodic core reference for this source shape"
    if role == "same_position_scaled_member":
        return "same source shape appears at the same positions under a scaled periodic core"
    return "same source shape appears without a direct periodic-core multiplier"


def _next_source_shape_member_sort_key(
    row: Mapping[str, Any]
) -> tuple[int, int, int, int, int]:
    multiplier = row.get("same_core_multiplier")
    multiplier_rank = int(multiplier) if multiplier is not None else 999999
    return (
        multiplier_rank,
        int(row["base"]),
        int(row["n"]),
        int(row["certified_lookahead_blocks"]),
        int(row["exact_gap_numerator"]),
    )


def _next_source_shape_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    skipped_signatures: Sequence[str],
    selected_shape: Mapping[str, Any] | None,
    all_members: Sequence[dict[str, Any]],
    emitted_members: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    n_values = sorted({int(row["n"]) for row in all_members})
    multipliers = sorted(
        {
            int(row["same_core_multiplier"])
            for row in all_members
            if row.get("same_core_multiplier") is not None
        }
    )
    return {
        "group": OBSERVABILITY_NEXT_SOURCE_SHAPE_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "source_symmetry_signature": (
            selected_shape.get("source_symmetry_signature") if selected_shape else None
        ),
        "skipped_source_symmetry_signatures": list(skipped_signatures),
        "selected_shape_rank": selected_shape.get("shape_rank") if selected_shape else None,
        "family_class": "next_unresolved_source_shape_family",
        "total_members": len(all_members),
        "emitted_members": len(emitted_members),
        "n_values": n_values,
        "same_core_multipliers": multipliers,
        "bases_observed": (
            list(selected_shape.get("bases_observed", [])) if selected_shape else []
        ),
        "hidden_bases": (
            list(selected_shape.get("hidden_bases", [])) if selected_shape else []
        ),
        "visible_bases": (
            list(selected_shape.get("visible_bases", [])) if selected_shape else []
        ),
        "shifted_bases": (
            list(selected_shape.get("shifted_bases", [])) if selected_shape else []
        ),
        "canonical_conflict_positions": (
            list(selected_shape.get("canonical_conflict_positions", []))
            if selected_shape
            else []
        ),
        "exact_position_signatures": (
            list(selected_shape.get("exact_position_signatures", []))
            if selected_shape
            else []
        ),
        "min_certified_lookahead_blocks": (
            selected_shape.get("min_certified_lookahead_blocks")
            if selected_shape
            else None
        ),
        "min_exact_gap_numerator": (
            selected_shape.get("min_exact_gap_numerator") if selected_shape else None
        ),
        "lean_ready_member_count": sum(
            1
            for row in all_members
            if row["lean_readiness"] == "existing_composite68_family_theorem"
        ),
        "same_core_shift_proved_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"]
            == "same_core_shift_proved_by_arithmetic_criterion"
        ),
        "same_core_shift_candidate_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"] == "same_core_shift_criterion_candidate"
        ),
        "finite_only_hidden_conflict_cases": sum(
            1
            for row in all_members
            if row["same_core_shift_support_status"] == "finite_only_hidden_conflict"
        ),
        "observability_boundary_status": (
            "empirical_open_boundary_next_source_shape_family_classifier"
        ),
        "recommended_next_observability_task": (
            "classify_next_source_shape_family_or_add_finite_package"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_next_source_shape_family_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
    skipped_signatures: Sequence[str] = DEFAULT_SETTLED_SOURCE_SHAPE_SIGNATURES,
) -> list[dict[str, Any]]:
    """Classify the first unresolved source-shape family after settled shapes."""

    parsed_bases = _parse_bases(bases)
    skipped = tuple(skipped_signatures)
    comparison_rows = observability_instrument_comparison_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    shape_rows = [
        row
        for row in comparison_rows
        if row.get("group") == OBSERVABILITY_SOURCE_SHAPE_GROUP
    ]
    selected_shape = next(
        (
            row
            for row in shape_rows
            if str(row.get("source_symmetry_signature")) not in skipped
        ),
        None,
    )
    selected_signature = (
        str(selected_shape["source_symmetry_signature"]) if selected_shape else None
    )
    members = [
        row
        for row in comparison_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature") == selected_signature
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    canonical_positions = (
        list(selected_shape.get("canonical_conflict_positions", []))
        if selected_shape
        else []
    )
    for row in members:
        exported = dict(row)
        positions = list(row.get("conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        periodic_modulus = int(row["periodic_modulus"])
        same_core_multiplier = (
            int(row["n"]) // periodic_modulus
            if int(row["n"]) % periodic_modulus == 0
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_NEXT_SOURCE_SHAPE_MEMBER_GROUP,
                "family_class": "next_unresolved_source_shape_family",
                "source_shape_selection_reason": (
                    "first_unsettled_after_skipped_signatures"
                ),
                "skipped_source_symmetry_signatures": list(skipped),
                "instrument_shape_rank": row.get("shape_rank"),
                "instrument_member_rank": row.get("member_rank"),
                "selected_shape_rank": selected_shape.get("shape_rank")
                if selected_shape
                else None,
                "source_symmetry_family_role": _generic_source_shape_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "next_source_shape_family_note": _generic_source_shape_family_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_next_source_shape_family_classifier"
                ),
                "next_observability_task": (
                    "classify_next_source_shape_family_or_add_finite_package"
                ),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_next_source_shape_member_sort_key)
    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank
    if top and top > 0:
        emitted_members = classified_members[:top]
    else:
        emitted_members = classified_members
    return [
        _next_source_shape_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            skipped_signatures=skipped,
            selected_shape=selected_shape,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _shape187_family_role(row: Mapping[str, Any]) -> str:
    multiplier = (
        int(row["n"]) // 187 if int(row["n"]) % 187 == 0 else None
    )
    if multiplier == 2:
        return "double_core_same_position_member"
    if multiplier == 4:
        return "quadruple_core_same_position_member"
    if multiplier == 1:
        return "periodic_core_reference"
    return "same_position_scaled_member"


def _shape187_family_bridge_note(row: Mapping[str, Any]) -> str:
    role = _shape187_family_role(row)
    if role == "double_core_same_position_member":
        return "N=374 is the double-core same-position member for Shape187/K188"
    if role == "quadruple_core_same_position_member":
        return "N=748 is the quadruple-core same-position member for Shape187/K188"
    if role == "periodic_core_reference":
        return "N=187 is the periodic core reference if it appears under wider bounds"
    return "same source shape with same-position hidden carried-output behavior"


def _shape187_same_position_scaling_fields(row: Mapping[str, Any]) -> dict[str, Any]:
    periodic_modulus = int(row["periodic_modulus"])
    denominator = int(row["n"])
    block_base = int(row["B"])
    remainder_k = int(row["k"])
    multiplier = (
        denominator // periodic_modulus
        if denominator % periodic_modulus == 0
        else None
    )
    positions = [int(position) for position in row.get("conflict_positions") or []]
    coefficients = [
        int(coefficient) for coefficient in row.get("conflict_coefficients") or []
    ]
    carry_states = [int(carry) for carry in row.get("conflict_carry_states") or []]
    block_values = [int(value) for value in row.get("conflict_block_values") or []]
    coefficient_ratio = None
    if len(coefficients) == 2 and coefficients[0] != 0:
        if coefficients[1] % coefficients[0] == 0:
            coefficient_ratio = coefficients[1] // coefficients[0]

    expected_carry_states = [
        (remainder_k ** (position + 1)) // denominator for position in positions
    ]
    block_formula_holds = (
        len(coefficients) == len(carry_states) == len(block_values)
        and all(
            (coefficient + carry) % block_base == block_value
            for coefficient, carry, block_value in zip(
                coefficients, carry_states, block_values
            )
        )
    )
    hidden_output_formula_holds = (
        bool(row.get("conflict_output_hidden"))
        and len(set(block_values)) == 1
        and block_formula_holds
    )
    same_position_scaling_hypotheses_hold = all(
        [
            periodic_modulus == 187,
            remainder_k == 188,
            remainder_k == periodic_modulus + 1,
            multiplier is not None and multiplier > 1,
            multiplier is not None
            and (periodic_modulus + 1) % multiplier == 0,
            (remainder_k * remainder_k) % denominator == remainder_k,
            positions == [1, 2],
            coefficient_ratio == remainder_k,
            carry_states == expected_carry_states,
            hidden_output_formula_holds,
        ]
    )
    named_instantiation = SHAPE187_K188_NAMED_SAME_POSITION_INSTANTIATIONS.get(
        (int(row["base"]), denominator)
    )
    named_hypothesis_instantiation = (
        SHAPE187_K188_NAMED_SAME_POSITION_HYPOTHESIS_INSTANTIATIONS.get(
            (int(row["base"]), denominator)
        )
    )
    named_finite_conflict_instantiation = (
        SHAPE187_K188_NAMED_FINITE_CONFLICT_INSTANTIATIONS.get(
            (int(row["base"]), denominator)
        )
    )
    if same_position_scaling_hypotheses_hold:
        if named_instantiation is not None:
            status = "same_position_scaling_proved_by_arithmetic_criterion"
            proof_surface = "lean_named_arithmetic_criterion"
            failure_reason = None
        else:
            status = "same_position_scaling_criterion_candidate"
            proof_surface = "exported_idempotent_remainder_hypotheses"
            failure_reason = "no_named_lean_instantiation"
    else:
        status = "finite_only_hidden_conflict"
        proof_surface = "finite_conflict_record_only"
        failure_reason = "same_position_scaling_hypotheses_not_satisfied"

    return {
        "same_position_scaling_support_status": status,
        "same_position_scaling_proof_surface": proof_surface,
        "same_position_scaling_core_modulus": periodic_modulus,
        "same_position_scaling_multiplier": multiplier,
        "same_position_scaling_positions": positions,
        "same_position_scaling_idempotent_remainder": (
            (remainder_k * remainder_k) % denominator == remainder_k
        ),
        "same_position_hyp_k_eq_core_plus_one": (
            remainder_k == periodic_modulus + 1
        ),
        "same_position_hyp_multiplier_divides_k": (
            multiplier is not None and remainder_k % multiplier == 0
        ),
        "same_position_hyp_coefficient_ratio_eq_k": (
            coefficient_ratio == remainder_k
        ),
        "same_position_hyp_carry_states_match_floor_powers": (
            carry_states == expected_carry_states
        ),
        "same_position_hyp_hidden_output_formula_holds": (
            hidden_output_formula_holds
        ),
        "same_position_scaling_coefficient_ratio": coefficient_ratio,
        "same_position_scaling_expected_carry_states": expected_carry_states,
        "same_position_scaling_suggested_lean_theorem": (
            SAME_POSITION_IDEMPOTENT_GENERIC_CRITERION_THEOREM
            if same_position_scaling_hypotheses_hold
            else None
        ),
        "same_position_scaling_criterion_theorem": (
            SAME_POSITION_IDEMPOTENT_GENERIC_CRITERION_THEOREM
            if same_position_scaling_hypotheses_hold
            else None
        ),
        "same_position_scaling_exported_hypothesis_record": (
            SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_RECORD
            if same_position_scaling_hypotheses_hold
            else None
        ),
        "same_position_scaling_idempotent_remainder_projection": (
            SAME_POSITION_SCALING_IDEMPOTENT_REMAINDER_PROJECTION
            if same_position_scaling_hypotheses_hold
            else None
        ),
        "same_position_scaling_exported_hypothesis_adapter": (
            SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_ADAPTER
            if same_position_scaling_hypotheses_hold
            else None
        ),
        "same_position_scaling_intended_proof_path": (
            [
                SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_RECORD,
                SAME_POSITION_SCALING_IDEMPOTENT_REMAINDER_PROJECTION,
                SAME_POSITION_IDEMPOTENT_GENERIC_CRITERION_THEOREM,
                SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_ADAPTER,
            ]
            if same_position_scaling_hypotheses_hold
            else []
        ),
        "same_position_scaling_named_hypothesis_instantiation": (
            named_hypothesis_instantiation
        ),
        "same_position_scaling_named_finite_conflict_instantiation": (
            named_finite_conflict_instantiation
        ),
        "same_position_scaling_named_instantiation": named_instantiation,
        "same_position_scaling_failure_reason": failure_reason,
    }


def _shape187_member_sort_key(row: Mapping[str, Any]) -> tuple[int, int, int, int, int]:
    multiplier = row.get("same_core_multiplier")
    multiplier_rank = int(multiplier) if multiplier is not None else 999999
    return (
        int(row["exact_gap_numerator"]),
        int(row["certified_lookahead_blocks"]),
        multiplier_rank,
        int(row["base"]),
        int(row["n"]),
    )


def _shape187_family_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    all_members: Sequence[dict[str, Any]],
    emitted_members: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    n_values = sorted({int(row["n"]) for row in all_members})
    multipliers = sorted(
        {
            int(row["same_core_multiplier"])
            for row in all_members
            if row.get("same_core_multiplier") is not None
        }
    )
    first_package = min(
        all_members,
        key=lambda row: (
            int(row["exact_gap_numerator"]),
            int(row["certified_lookahead_blocks"]),
            int(row["base"]),
            int(row["n"]),
        ),
        default=None,
    )
    return {
        "group": OBSERVABILITY_SHAPE187_K188_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "source_symmetry_signature": SHAPE187_K188_SOURCE_SYMMETRY_SIGNATURE,
        "family_class": "shape187_k188_same_position_scaling",
        "total_members": len(all_members),
        "emitted_members": len(emitted_members),
        "n_values": n_values,
        "same_core_multipliers": multipliers,
        "bases_observed": sorted({int(row["base"]) for row in all_members}),
        "same_position_scaling_proved_cases": sum(
            1
            for row in all_members
            if row["same_position_scaling_support_status"]
            == "same_position_scaling_proved_by_arithmetic_criterion"
        ),
        "same_position_scaling_candidate_cases": sum(
            1
            for row in all_members
            if row["same_position_scaling_support_status"]
            == "same_position_scaling_criterion_candidate"
        ),
        "finite_only_hidden_conflict_cases": sum(
            1
            for row in all_members
            if row["same_position_scaling_support_status"]
            == "finite_only_hidden_conflict"
        ),
        "all_members_idempotent_remainder": all(
            bool(row["same_position_scaling_idempotent_remainder"])
            for row in all_members
        ),
        "all_members_hidden_output_formula_holds": all(
            bool(row["same_position_hyp_hidden_output_formula_holds"])
            for row in all_members
        ),
        "first_finite_package_tuple": (
            [
                int(first_package["base"]),
                int(first_package["n"]),
                int(first_package["m"]),
                int(first_package["B"]),
                int(first_package["q"]),
                int(first_package["k"]),
                int(first_package["certified_lookahead_blocks"]),
                int(first_package["exact_gap_numerator"]),
            ]
            if first_package is not None
            else None
        ),
        "first_finite_package_namespace": (
            f"QRTour.FutureBase{int(first_package['base'])}N{int(first_package['n'])}"
            if first_package is not None
            else None
        ),
        "first_finite_package_theorem": (
            "coordinate_stateAlignments_one_two_certifiedConflict_eight_one"
            if first_package is not None
            and int(first_package["certified_lookahead_blocks"]) == 1
            else "coordinate_stateAlignments_one_two_certifiedConflict_eight_two"
            if first_package is not None
            else None
        ),
        "same_position_scaling_suggested_lean_theorem": (
            SAME_POSITION_IDEMPOTENT_GENERIC_CRITERION_THEOREM
        ),
        "same_position_scaling_exported_hypothesis_record": (
            SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_RECORD
        ),
        "same_position_scaling_idempotent_remainder_projection": (
            SAME_POSITION_SCALING_IDEMPOTENT_REMAINDER_PROJECTION
        ),
        "same_position_scaling_exported_hypothesis_adapter": (
            SAME_POSITION_SCALING_EXPORTED_HYPOTHESIS_ADAPTER
        ),
        "observability_boundary_status": (
            "empirical_open_boundary_shape187_k188_family_classifier"
        ),
        "recommended_next_observability_task": (
            "extend_same_position_idempotent_criterion_to_remaining_shape187_rows_or_add_next_finite_package"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_shape187_k188_family_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Classify the Shape187/K188 same-position scaling source-shape family."""

    parsed_bases = _parse_bases(bases)
    comparison_rows = observability_instrument_comparison_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    members = [
        row
        for row in comparison_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature")
        == SHAPE187_K188_SOURCE_SYMMETRY_SIGNATURE
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    for row in members:
        exported = dict(row)
        same_core_multiplier = (
            int(row["n"]) // 187 if int(row["n"]) % 187 == 0 else None
        )
        positions = list(row.get("conflict_positions") or [])
        canonical_positions = list(row.get("canonical_conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE187_K188_MEMBER_GROUP,
                "family_class": "shape187_k188_same_position_scaling",
                "source_symmetry_family_role": _shape187_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "shape187_family_bridge_note": _shape187_family_bridge_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_shape187_k188_family_classifier"
                ),
                "next_observability_task": (
                    "extend_same_position_idempotent_criterion_to_remaining_shape187_rows_or_add_next_finite_package"
                ),
                **_shape187_same_position_scaling_fields(row),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_shape187_member_sort_key)
    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank
    if top and top > 0:
        emitted_members = classified_members[:top]
    else:
        emitted_members = classified_members
    return [
        _shape187_family_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _is_positive_reconstruction_candidate(row: Mapping[str, Any]) -> bool:
    return (
        row.get("coefficient_observability_class")
        == "coefficient_functional_frontier"
        and _target_functional(row, "raw_coefficient_nat") is True
        and _target_functional(row, "coefficient_mod_block_base") is True
        and _target_functional(row, "carried_block_value") is True
        and _target_functional(row, "carry_state") is True
    )


def _positive_reconstruction_sort_key(
    row: Mapping[str, Any],
) -> tuple[int, int, int, int, int]:
    return (
        int(row["exact_gap_numerator"]),
        int(row["certified_lookahead_blocks"]),
        int(row["k"]),
        int(row["n"]),
        int(row["base"]),
    )


def _positive_reconstruction_source_pin_fields(
    row: Mapping[str, Any],
) -> dict[str, Any]:
    anchor = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS.get(
        (int(row["base"]), int(row["n"]))
    )
    if anchor is None:
        return {
            "positive_reconstruction_source_pinned": False,
            "positive_reconstruction_source_status": "empirical_frontier_only",
            "positive_reconstruction_lean_support_status": "empirical_frontier_only",
            "positive_reconstruction_namespace": None,
            "positive_reconstruction_module_path": None,
            "positive_reconstruction_functional_theorem": None,
            "positive_reconstruction_factor_through_theorem": None,
            "positive_reconstruction_qualified_theorem_names": [],
        }
    namespace = str(anchor["namespace"])
    functional_theorem = str(anchor["functional_theorem_name"])
    factor_through_theorem = str(anchor["factor_through_theorem_name"])
    return {
        "positive_reconstruction_source_pinned": True,
        "positive_reconstruction_source_status": SOURCE_PINNED_FIXTURE_STATUS,
        "positive_reconstruction_lean_support_status": (
            "source_pinned_finite_factor_through_theorem"
        ),
        "positive_reconstruction_namespace": namespace,
        "positive_reconstruction_module_path": anchor["module_path"],
        "positive_reconstruction_functional_theorem": functional_theorem,
        "positive_reconstruction_factor_through_theorem": factor_through_theorem,
        "positive_reconstruction_qualified_theorem_names": [
            f"{namespace}.{functional_theorem}",
            f"{namespace}.{factor_through_theorem}",
        ],
    }


def _positive_reconstruction_power_no_collision_fields(
    row: Mapping[str, Any],
    *,
    is_source_pinned: bool,
) -> dict[str, Any]:
    requested_blocks = int(row.get("requested_blocks", 0))
    modulus = int(row["n"])
    remainder_k = int(row["k"])
    unreduced_window = [
        remainder_k**index
        for index in range(requested_blocks)
    ]
    window = [
        pow(remainder_k, index, modulus)
        for index in range(requested_blocks)
    ]
    distinct_count = len(set(window))
    injective_window = distinct_count == len(window)
    no_wrap = 1 < remainder_k and all(value < modulus for value in unreduced_window)
    if injective_window and is_source_pinned:
        status = "source_pinned_power_no_collision_sufficient_criterion_satisfied"
    elif injective_window:
        status = "empirical_power_no_collision_sufficient_criterion_satisfied"
    else:
        status = "power_no_collision_criterion_not_satisfied"
    if no_wrap and is_source_pinned:
        no_wrap_status = "source_pinned_power_no_wrap_sufficient_criterion_satisfied"
    elif no_wrap:
        no_wrap_status = "empirical_power_no_wrap_sufficient_criterion_satisfied"
    else:
        no_wrap_status = "power_no_wrap_criterion_not_satisfied"
    return {
        "positive_reconstruction_power_no_collision_criterion_id": (
            POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_ID
        ),
        "positive_reconstruction_power_no_collision_criterion_formula": (
            POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_FORMULA
        ),
        "positive_reconstruction_power_no_wrap_criterion_id": (
            POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_ID
        ),
        "positive_reconstruction_power_no_wrap_criterion_formula": (
            POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_FORMULA
        ),
        "remainder_power_unreduced_window": unreduced_window,
        "remainder_power_residue_window": window,
        "remainder_power_residue_window_distinct_count": distinct_count,
        "positive_reconstruction_hyp_remainder_power_residue_window_injective": (
            injective_window
        ),
        "positive_reconstruction_power_no_collision_criterion_status": status,
        "positive_reconstruction_hyp_remainder_power_residue_no_wrap": no_wrap,
        "positive_reconstruction_power_no_wrap_criterion_status": no_wrap_status,
    }


def _is_positive_reconstruction_base7_k3_family_row(row: Mapping[str, Any]) -> bool:
    return (
        int(row["base"]) == 7
        and int(row["B"]) == 343
        and int(row["k"]) == 3
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base7_stride4_k3_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 7
        and int(row["B"]) == 2401
        and int(row["k"]) == 3
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base7_stride6_k4_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 7
        and int(row["B"]) == 117649
        and int(row["k"]) == 4
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_MODULI
    )


def _is_positive_reconstruction_base7_stride6_k3_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 7
        and int(row["B"]) == 117649
        and int(row["k"]) == 3
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base30_k3_family_row(row: Mapping[str, Any]) -> bool:
    return (
        int(row["base"]) == 30
        and int(row["B"]) == 900
        and int(row["k"]) == 3
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base30_stride3_k4_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 30
        and int(row["B"]) == 27000
        and int(row["k"]) == 4
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_MODULI
    )


def _is_positive_reconstruction_base10_k4_family_row(row: Mapping[str, Any]) -> bool:
    return (
        int(row["base"]) == 10
        and int(row["B"]) == 1000
        and int(row["k"]) == 4
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_MODULI
    )


def _is_positive_reconstruction_base10_stride4_k4_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 10
        and int(row["B"]) == 10000
        and int(row["k"]) == 4
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_MODULI
    )


def _is_positive_reconstruction_base10_stride5_k6_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 10
        and int(row["B"]) == 100000
        and int(row["k"]) == 6
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_MODULI
    )


def _is_positive_reconstruction_base10_stride5_k4_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 10
        and int(row["B"]) == 100000
        and int(row["k"]) == 4
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_MODULI
    )


def _is_positive_reconstruction_base12_stride2_k3_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 12
        and int(row["B"]) == 144
        and int(row["k"]) == 3
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base12_stride5_k3_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 12
        and int(row["B"]) == 248832
        and int(row["k"]) == 3
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base12_k3_family_row(row: Mapping[str, Any]) -> bool:
    return (
        int(row["base"]) == 12
        and int(row["B"]) == 1728
        and int(row["k"]) == 3
        and int(row["n"]) in POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_MODULI
    )


def _is_positive_reconstruction_base12_stride4_k4_family_row(
    row: Mapping[str, Any],
) -> bool:
    return (
        int(row["base"]) == 12
        and int(row["B"]) == 20736
        and int(row["k"]) == 4
        and int(row["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_MODULI
    )


def _positive_reconstruction_frontier_coverage_fields(
    row: Mapping[str, Any],
    *,
    source_pin_fields: Mapping[str, Any],
    criterion_fields: Mapping[str, Any],
) -> dict[str, Any]:
    if source_pin_fields.get("positive_reconstruction_source_pinned") is True:
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                "source_pinned_finite_factor_through_theorem"
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                source_pin_fields.get("positive_reconstruction_factor_through_theorem")
            ),
            "positive_reconstruction_frontier_coverage_moduli": [],
        }
    if _is_positive_reconstruction_base7_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base7_stride4_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base7_stride6_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base7_stride6_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base30_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base30_stride3_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base10_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base10_stride4_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base10_stride5_k6_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base10_stride5_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base12_stride2_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base12_stride5_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base12_k3_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_MODULI
            ),
        }
    if _is_positive_reconstruction_base12_stride4_k4_family_row(row):
        return {
            "positive_reconstruction_frontier_covered": True,
            "positive_reconstruction_frontier_coverage_status": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_CRITERION_STATUS
            ),
            "positive_reconstruction_frontier_coverage_theorem": (
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM
            ),
            "positive_reconstruction_frontier_coverage_moduli": list(
                POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_MODULI
            ),
        }
    if (
        criterion_fields.get(
            "positive_reconstruction_hyp_remainder_power_residue_window_injective"
        )
        is True
    ):
        return {
            "positive_reconstruction_frontier_covered": False,
            "positive_reconstruction_frontier_coverage_status": (
                "empirical_uncovered_power_no_collision_frontier"
            ),
            "positive_reconstruction_frontier_coverage_theorem": None,
            "positive_reconstruction_frontier_coverage_moduli": [],
        }
    return {
        "positive_reconstruction_frontier_covered": False,
        "positive_reconstruction_frontier_coverage_status": (
            "not_power_no_collision_frontier"
        ),
        "positive_reconstruction_frontier_coverage_theorem": None,
        "positive_reconstruction_frontier_coverage_moduli": [],
    }


def _positive_reconstruction_arithmetic_criterion_fields(
    row: Mapping[str, Any],
    *,
    is_source_pinned: bool,
) -> dict[str, Any]:
    injective_window = bool(row.get("remainder_state_window_injective"))
    functional = bool(row.get("remainder_to_coefficient_functional"))
    if injective_window and is_source_pinned:
        status = "source_pinned_sufficient_criterion_satisfied"
        failure_reason = None
        next_task = "prove_finite_injective_readout_reconstruction_lemma"
    elif injective_window:
        status = "empirical_sufficient_criterion_satisfied"
        failure_reason = None
        next_task = "source_pin_or_prove_finite_injective_readout_hook"
    elif functional:
        status = "functional_but_injective_readout_criterion_not_satisfied"
        failure_reason = "repeated_remainder_state_requires_coefficient_consistency"
        next_task = "mine_noninjective_functional_reconstruction_condition"
    else:
        status = "criterion_not_satisfied"
        failure_reason = "remainder_to_coefficient_not_functional"
        next_task = "not_a_positive_reconstruction_candidate"
    power_no_collision_fields = _positive_reconstruction_power_no_collision_fields(
        row, is_source_pinned=is_source_pinned
    )
    return {
        "positive_reconstruction_arithmetic_criterion_id": (
            POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_ID
        ),
        "positive_reconstruction_arithmetic_criterion_formula": (
            POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_FORMULA
        ),
        "positive_reconstruction_arithmetic_criterion_status": status,
        "positive_reconstruction_hyp_remainder_state_window_injective": injective_window,
        "positive_reconstruction_hyp_distinct_remainder_state_count": row.get(
            "remainder_state_window_distinct_count"
        ),
        "positive_reconstruction_hyp_requested_blocks": row.get("requested_blocks"),
        "positive_reconstruction_criterion_failure_reason": failure_reason,
        "positive_reconstruction_criterion_next_lean_task": next_task,
        **power_no_collision_fields,
    }


def _positive_reconstruction_candidate_row(
    row: Mapping[str, Any], rank: int
) -> dict[str, Any]:
    exported = dict(row)
    source_pin_fields = _positive_reconstruction_source_pin_fields(row)
    is_source_pinned = bool(source_pin_fields["positive_reconstruction_source_pinned"])
    criterion_fields = _positive_reconstruction_arithmetic_criterion_fields(
        row, is_source_pinned=is_source_pinned
    )
    frontier_coverage_fields = _positive_reconstruction_frontier_coverage_fields(
        row,
        source_pin_fields=source_pin_fields,
        criterion_fields=criterion_fields,
    )
    exported.update(
        {
            "group": OBSERVABILITY_POSITIVE_RECONSTRUCTION_CANDIDATE_GROUP,
            "positive_reconstruction_rank": rank,
            "positive_reconstruction_status": (
                "source_pinned_finite_factor_through_theorem"
                if is_source_pinned
                else "finite_factor_through_candidate"
            ),
            "factor_through_observation": "remainder_state",
            "factor_through_targets": [
                "raw_coefficient_nat",
                "coefficient_mod_block_base",
                "carried_block_value",
                "carry_state",
            ],
            "factor_through_target": "raw_coefficient_nat",
            "factor_through_surface": (
                "List.FunctionalOnFst_equiv_FactorsThrough_finite_member_subtype"
            ),
            "lean_bridge_surface": (
                "FactorsThrough_and_List.FunctionalOnFst_equivalence"
            ),
            "arithmetic_reconstruction_status": "future_theorem_work",
            "next_positive_reconstruction_task": (
                criterion_fields["positive_reconstruction_criterion_next_lean_task"]
            ),
            "observability_boundary_status": (
                "empirical_open_boundary_positive_reconstruction_candidate"
            ),
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            **source_pin_fields,
            **criterion_fields,
            **frontier_coverage_fields,
        }
    )
    return exported


def _program_family_row(
    *,
    lane_rank: int,
    family_id: str,
    lane_id: str,
    summary: Mapping[str, Any] | None,
    family_label: str,
    support_status: str,
    next_task: str,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "group": OBSERVABILITY_PROGRAM_FAMILY_GROUP,
        "program_lane_rank": lane_rank,
        "program_lane_id": lane_id,
        "program_family_id": family_id,
        "program_family_label": family_label,
        "program_family_support_status": support_status,
        "next_observability_task": next_task,
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }
    if summary is not None:
        for key in (
            "source_symmetry_signature",
            "family_class",
            "total_members",
            "n_values",
            "bases_observed",
            "same_core_shift_proved_cases",
            "same_core_shift_candidate_cases",
            "finite_only_hidden_conflict_cases",
            "mod_stable_shift_proved_cases",
            "mod_stable_shift_candidate_cases",
            "finite_only_mod_stable_carry_loss_cases",
            "same_position_scaling_proved_cases",
            "same_position_scaling_candidate_cases",
            "target_signature_family_class",
            "member_count",
            "functional_frontier_cases",
            "representative_tuple",
        ):
            if key in summary:
                row[key] = summary[key]
    return row


def _program_lane_rows(
    *,
    shape17_summary: Mapping[str, Any] | None,
    shape187_summary: Mapping[str, Any] | None,
    shape13_summary: Mapping[str, Any] | None,
    unresolved_summary: Mapping[str, Any] | None,
    positive_candidates: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    positive_proof_covered_count = sum(
        1
        for row in positive_candidates
        if row.get("positive_reconstruction_source_pinned") is True
    )
    positive_empirical_count = len(positive_candidates) - positive_proof_covered_count
    positive_injective_criterion_count = sum(
        1
        for row in positive_candidates
        if row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
    )
    positive_frontier_decision_fields = (
        _positive_reconstruction_frontier_decision_fields(positive_candidates)
    )
    lanes = [
        {
            "program_lane_rank": 1,
            "program_lane_id": "composite68_shape17_obstruction_lane",
            "program_lane_label": "Composite68 / Shape17 proof-backed obstruction lane",
            "program_lane_status": "proof_backed_finite_hidden_obstruction_lane",
            "program_lane_support_surface": "observability-shape17-k4-family",
            "member_count": (
                int(shape17_summary.get("total_members", 0))
                if shape17_summary
                else 0
            ),
            "proof_covered_count": (
                int(shape17_summary.get("same_core_shift_proved_cases", 0))
                if shape17_summary
                else 0
            ),
            "candidate_count": (
                int(shape17_summary.get("same_core_shift_candidate_cases", 0))
                if shape17_summary
                else 0
            ),
            "recommended_next_observability_task": (
                "use_as_obstruction_flagship_while_mining_positive_reconstruction"
            ),
        },
        {
            "program_lane_rank": 2,
            "program_lane_id": "shape187_same_position_scaling_lane",
            "program_lane_label": "Shape187/K188 same-position scaling lane",
            "program_lane_status": "partially_proof_backed_hidden_obstruction_lane",
            "program_lane_support_surface": "observability-shape187-k188-family",
            "member_count": (
                int(shape187_summary.get("total_members", 0))
                if shape187_summary
                else 0
            ),
            "proof_covered_count": (
                int(shape187_summary.get("same_position_scaling_proved_cases", 0))
                if shape187_summary
                else 0
            ),
            "candidate_count": (
                int(shape187_summary.get("same_position_scaling_candidate_cases", 0))
                if shape187_summary
                else 0
            ),
            "recommended_next_observability_task": (
                "finish_or_bound_same_position_scaling_arithmetic_candidates"
            ),
        },
        {
            "program_lane_rank": 3,
            "program_lane_id": "shape13_mod_stable_carry_loss_lane",
            "program_lane_label": "Shape13/K4 mod-stable carry-loss lane",
            "program_lane_status": "target_split_loss_pattern_lane",
            "program_lane_support_surface": (
                "observability-shape13-k4-mod-stable-carry-loss"
            ),
            "member_count": (
                int(shape13_summary.get("total_members", 0))
                if shape13_summary
                else 0
            ),
            "proof_covered_count": (
                int(shape13_summary.get("mod_stable_shift_proved_cases", 0))
                if shape13_summary
                else 0
            ),
            "candidate_count": (
                int(shape13_summary.get("mod_stable_shift_candidate_cases", 0))
                if shape13_summary
                else 0
            ),
            "recommended_next_observability_task": (
                "reuse_scale_two_bundle_when_new_shape13_members_appear"
            ),
        },
        {
            "program_lane_rank": 4,
            "program_lane_id": "unresolved_hidden_conflict_lane",
            "program_lane_label": "Unresolved hidden-conflict families",
            "program_lane_status": "finite_only_hidden_conflict_family_lane",
            "program_lane_support_surface": "observability-next-source-shape-family",
            "member_count": (
                int(unresolved_summary.get("total_members", 0))
                if unresolved_summary
                else 0
            ),
            "proof_covered_count": 0,
            "candidate_count": (
                int(unresolved_summary.get("finite_only_hidden_conflict_cases", 0))
                if unresolved_summary
                else 0
            ),
            "recommended_next_observability_task": (
                "promote_only_if_unresolved_family_signal_beats_reconstruction_signal"
            ),
        },
        {
            "program_lane_rank": 5,
            "program_lane_id": "positive_reconstruction_lane",
            "program_lane_label": "Positive reconstruction candidates",
            "program_lane_status": "partially_source_pinned_factor_through_candidate_lane",
            "program_lane_support_surface": (
                "observability-positive-reconstruction-candidate rows"
            ),
            "member_count": len(positive_candidates),
            "proof_covered_count": positive_proof_covered_count,
            "source_pinned_positive_reconstruction_cases": positive_proof_covered_count,
            "candidate_count": positive_empirical_count,
            "empirical_positive_reconstruction_candidates": positive_empirical_count,
            "injective_window_criterion_cases": positive_injective_criterion_count,
            "source_pinned_injective_window_criterion_cases": sum(
                1
                for row in positive_candidates
                if row.get("positive_reconstruction_source_pinned") is True
                and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
                is True
            ),
            "recommended_next_observability_task": (
                positive_frontier_decision_fields[
                    "recommended_positive_reconstruction_next_task"
                ]
            ),
        },
    ]
    for lane in lanes:
        lane.update(
            {
                "group": OBSERVABILITY_PROGRAM_LANE_GROUP,
                "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
                "observability_boundary_status": (
                    "empirical_open_boundary_program_lane"
                ),
            }
        )
    return lanes


def _first_unpinned_positive_power_no_collision_row(
    positive_candidates: Sequence[dict[str, Any]],
) -> dict[str, Any] | None:
    for row in positive_candidates:
        if (
            row.get("positive_reconstruction_source_pinned") is False
            and row.get(
                "positive_reconstruction_hyp_remainder_power_residue_window_injective"
            )
            is True
        ):
            return row
    return None


def _first_uncovered_positive_power_no_collision_row(
    positive_candidates: Sequence[dict[str, Any]],
) -> dict[str, Any] | None:
    for row in positive_candidates:
        if (
            row.get("positive_reconstruction_source_pinned") is False
            and row.get("positive_reconstruction_frontier_covered") is False
            and row.get(
                "positive_reconstruction_hyp_remainder_power_residue_window_injective"
            )
            is True
        ):
            return row
    return None


def _same_base_block_remainder_source_pinned_siblings(
    row: Mapping[str, Any] | None,
    positive_candidates: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    if row is None:
        return []
    base = int(row["base"])
    block_base = int(row["B"])
    remainder_k = int(row["k"])
    n = int(row["n"])
    return [
        candidate
        for candidate in positive_candidates
        if candidate.get("positive_reconstruction_source_pinned") is True
        and int(candidate["base"]) == base
        and int(candidate["B"]) == block_base
        and int(candidate["k"]) == remainder_k
        and int(candidate["n"]) != n
    ]


def _positive_reconstruction_frontier_decision_fields(
    positive_candidates: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    first_unpinned = _first_unpinned_positive_power_no_collision_row(
        positive_candidates
    )
    first_uncovered = _first_uncovered_positive_power_no_collision_row(
        positive_candidates
    )
    sibling_rows = _same_base_block_remainder_source_pinned_siblings(
        first_unpinned, positive_candidates
    )
    uncovered_sibling_rows = _same_base_block_remainder_source_pinned_siblings(
        first_uncovered, positive_candidates
    )
    if first_unpinned is None:
        return {
            "first_unpinned_positive_reconstruction_tuple": None,
            "first_unpinned_positive_reconstruction_status": None,
            "first_unpinned_positive_reconstruction_remainder_power_residue_window": [],
            "first_unpinned_positive_reconstruction_raw_coefficient_window": [],
            "first_unpinned_positive_reconstruction_family_seed_tuples": [],
            "first_unpinned_positive_reconstruction_family_signal": (
                "no_unpinned_power_no_collision_candidate_emitted"
            ),
            "first_uncovered_positive_reconstruction_tuple": None,
            "first_uncovered_positive_reconstruction_status": None,
            "first_uncovered_positive_reconstruction_remainder_power_residue_window": [],
            "first_uncovered_positive_reconstruction_raw_coefficient_window": [],
            "first_uncovered_positive_reconstruction_family_seed_tuples": [],
            "first_uncovered_positive_reconstruction_family_signal": (
                "no_uncovered_power_no_collision_candidate_emitted"
            ),
            "first_uncovered_positive_reconstruction_decision": (
                "mine_wider_bounds_for_uncovered_power_no_collision_candidates"
            ),
            "first_uncovered_positive_reconstruction_next_task": (
                "mine_wider_positive_reconstruction_candidates"
            ),
            "positive_reconstruction_family_criterion_status": (
                "no_family_criterion_selected"
            ),
            "positive_reconstruction_family_criterion_moduli": [],
            "positive_reconstruction_family_no_collision_theorem": None,
            "positive_reconstruction_family_functional_theorem": None,
            "positive_reconstruction_family_factor_through_theorem": None,
            "positive_reconstruction_family_pair_theorem": None,
            "recommended_positive_reconstruction_decision": (
                "mine_wider_bounds_for_power_no_collision_candidates"
            ),
            "recommended_positive_reconstruction_next_task": (
                "mine_wider_positive_reconstruction_candidates"
            ),
        }
    if first_uncovered is None:
        uncovered_fields = {
            "first_uncovered_positive_reconstruction_tuple": None,
            "first_uncovered_positive_reconstruction_status": None,
            "first_uncovered_positive_reconstruction_remainder_power_residue_window": [],
            "first_uncovered_positive_reconstruction_raw_coefficient_window": [],
            "first_uncovered_positive_reconstruction_family_seed_tuples": [],
            "first_uncovered_positive_reconstruction_family_signal": (
                "all_unpinned_power_no_collision_candidates_are_source_or_family_covered"
            ),
            "first_uncovered_positive_reconstruction_decision": (
                "mine_wider_bounds_for_uncovered_power_no_collision_candidates"
            ),
            "first_uncovered_positive_reconstruction_next_task": (
                "mine_wider_positive_reconstruction_candidates"
            ),
        }
    else:
        uncovered_family_signal = (
            "same_base_block_remainder_as_source_pinned_candidate"
            if uncovered_sibling_rows
            else "no_source_pinned_same_base_block_remainder_sibling"
        )
        if uncovered_sibling_rows:
            uncovered_decision = (
                "pursue_family_criterion_before_source_pinning_more_examples"
            )
            uncovered_next_task = (
                "prove_or_reject_same_base_block_remainder_power_no_collision_family"
            )
        else:
            uncovered_decision = (
                "inspect_as_standalone_near_power_or_order_boundary"
            )
            uncovered_next_task = (
                "prove_or_reject_first_uncovered_power_no_collision_order_boundary"
            )
        uncovered_fields = {
            "first_uncovered_positive_reconstruction_tuple": (
                _tuple_from_observability_row(first_uncovered)
            ),
            "first_uncovered_positive_reconstruction_status": first_uncovered.get(
                "positive_reconstruction_frontier_coverage_status"
            ),
            "first_uncovered_positive_reconstruction_remainder_power_residue_window": (
                first_uncovered.get("remainder_power_residue_window", [])
            ),
            "first_uncovered_positive_reconstruction_raw_coefficient_window": (
                first_uncovered.get("raw_coefficient_window", [])
            ),
            "first_uncovered_positive_reconstruction_family_seed_tuples": [
                _tuple_from_observability_row(sibling)
                for sibling in uncovered_sibling_rows
            ],
            "first_uncovered_positive_reconstruction_family_signal": (
                uncovered_family_signal
            ),
            "first_uncovered_positive_reconstruction_decision": uncovered_decision,
            "first_uncovered_positive_reconstruction_next_task": (
                uncovered_next_task
            ),
        }
    family_signal = (
        "same_base_block_remainder_as_source_pinned_candidate"
        if sibling_rows
        else "no_source_pinned_same_base_block_remainder_sibling"
    )
    is_base7_k3_family = (
        int(first_unpinned["base"]) == 7
        and int(first_unpinned["B"]) == 343
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_MODULI
    )
    is_base7_stride4_k3_family = (
        int(first_unpinned["base"]) == 7
        and int(first_unpinned["B"]) == 2401
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_MODULI
    )
    is_base7_stride6_k4_family = (
        int(first_unpinned["base"]) == 7
        and int(first_unpinned["B"]) == 117649
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_MODULI
    )
    is_base7_stride6_k3_family = (
        int(first_unpinned["base"]) == 7
        and int(first_unpinned["B"]) == 117649
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_MODULI
    )
    is_base30_k3_family = (
        int(first_unpinned["base"]) == 30
        and int(first_unpinned["B"]) == 900
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_MODULI
    )
    is_base30_stride3_k4_family = (
        int(first_unpinned["base"]) == 30
        and int(first_unpinned["B"]) == 27000
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_MODULI
    )
    is_base10_k4_family = (
        int(first_unpinned["base"]) == 10
        and int(first_unpinned["B"]) == 1000
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_MODULI
    )
    is_base10_stride4_k4_family = (
        int(first_unpinned["base"]) == 10
        and int(first_unpinned["B"]) == 10000
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_MODULI
    )
    is_base10_stride5_k6_family = (
        int(first_unpinned["base"]) == 10
        and int(first_unpinned["B"]) == 100000
        and int(first_unpinned["k"]) == 6
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_MODULI
    )
    is_base10_stride5_k4_family = (
        int(first_unpinned["base"]) == 10
        and int(first_unpinned["B"]) == 100000
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_MODULI
    )
    is_base12_stride2_k3_family = (
        int(first_unpinned["base"]) == 12
        and int(first_unpinned["B"]) == 144
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_MODULI
    )
    is_base12_stride5_k3_family = (
        int(first_unpinned["base"]) == 12
        and int(first_unpinned["B"]) == 248832
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_MODULI
    )
    is_base12_k3_family = (
        int(first_unpinned["base"]) == 12
        and int(first_unpinned["B"]) == 1728
        and int(first_unpinned["k"]) == 3
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_MODULI
    )
    is_base12_stride4_k4_family = (
        int(first_unpinned["base"]) == 12
        and int(first_unpinned["B"]) == 20736
        and int(first_unpinned["k"]) == 4
        and int(first_unpinned["n"])
        in POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_MODULI
    )
    if sibling_rows and is_base7_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = POSITIVE_RECONSTRUCTION_BASE7_K3_FAMILY_PAIR_THEOREM
    elif sibling_rows and is_base7_stride4_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE4_K3_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base7_stride6_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K4_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base7_stride6_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE7_STRIDE6_K3_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base30_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = POSITIVE_RECONSTRUCTION_BASE30_K3_FAMILY_PAIR_THEOREM
    elif sibling_rows and is_base30_stride3_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE30_STRIDE3_K4_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base10_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = POSITIVE_RECONSTRUCTION_BASE10_K4_FAMILY_PAIR_THEOREM
    elif sibling_rows and is_base10_stride4_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE4_K4_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base10_stride5_k6_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K6_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base10_stride5_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE10_STRIDE5_K4_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base12_stride2_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE2_K3_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base12_stride5_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE5_K3_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows and is_base12_k3_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = POSITIVE_RECONSTRUCTION_BASE12_K3_FAMILY_PAIR_THEOREM
    elif sibling_rows and is_base12_stride4_k4_family:
        decision = "use_lean_proved_family_criterion_before_source_pinning_more_examples"
        next_task = "mine_next_uncovered_power_no_collision_family_or_counterexample"
        family_criterion_status = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_CRITERION_STATUS
        )
        family_criterion_moduli = list(
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_MODULI
        )
        family_no_collision_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_NO_COLLISION_THEOREM
        )
        family_functional_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_FUNCTIONAL_THEOREM
        )
        family_factor_through_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_FACTOR_THROUGH_THEOREM
        )
        family_pair_theorem = (
            POSITIVE_RECONSTRUCTION_BASE12_STRIDE4_K4_FAMILY_PAIR_THEOREM
        )
    elif sibling_rows:
        decision = "pursue_family_criterion_before_source_pinning_more_examples"
        next_task = "prove_or_reject_same_base_block_remainder_power_no_collision_family"
        family_criterion_status = "same_base_block_remainder_family_unproved"
        family_criterion_moduli = []
        family_no_collision_theorem = None
        family_functional_theorem = None
        family_factor_through_theorem = None
        family_pair_theorem = None
    else:
        decision = "inspect_as_standalone_finite_reconstruction_candidate"
        next_task = "prove_or_reject_first_unpinned_finite_power_no_collision_candidate"
        family_criterion_status = "no_source_pinned_family_criterion"
        family_criterion_moduli = []
        family_no_collision_theorem = None
        family_functional_theorem = None
        family_factor_through_theorem = None
        family_pair_theorem = None
    return {
        "first_unpinned_positive_reconstruction_tuple": _tuple_from_observability_row(
            first_unpinned
        ),
        "first_unpinned_positive_reconstruction_status": first_unpinned.get(
            "positive_reconstruction_power_no_collision_criterion_status"
        ),
        "first_unpinned_positive_reconstruction_remainder_power_residue_window": (
            first_unpinned.get("remainder_power_residue_window", [])
        ),
        "first_unpinned_positive_reconstruction_raw_coefficient_window": (
            first_unpinned.get("raw_coefficient_window", [])
        ),
        "first_unpinned_positive_reconstruction_family_seed_tuples": [
            _tuple_from_observability_row(sibling) for sibling in sibling_rows
        ],
        "first_unpinned_positive_reconstruction_family_signal": family_signal,
        "positive_reconstruction_family_criterion_status": family_criterion_status,
        "positive_reconstruction_family_criterion_moduli": family_criterion_moduli,
        "positive_reconstruction_family_no_collision_theorem": (
            family_no_collision_theorem
        ),
        "positive_reconstruction_family_functional_theorem": (
            family_functional_theorem
        ),
        "positive_reconstruction_family_factor_through_theorem": (
            family_factor_through_theorem
        ),
        "positive_reconstruction_family_pair_theorem": family_pair_theorem,
        "recommended_positive_reconstruction_decision": decision,
        "recommended_positive_reconstruction_next_task": (
            uncovered_fields["first_uncovered_positive_reconstruction_next_task"]
            if first_uncovered is not None
            else next_task
        ),
        **uncovered_fields,
    }


def _program_next_task_rows(
    positive_candidates: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    frontier_fields = _positive_reconstruction_frontier_decision_fields(
        positive_candidates
    )
    frontier_tuple = frontier_fields.get("first_uncovered_positive_reconstruction_tuple")
    frontier_seeds = frontier_fields.get(
        "first_uncovered_positive_reconstruction_family_seed_tuples", []
    )
    frontier_task_id = str(
        frontier_fields.get("recommended_positive_reconstruction_next_task")
    )
    if frontier_task_id == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    ):
        frontier_description = (
            "Classify the same-base/block-remainder family for the first "
            f"source-unpinned and family-uncovered power-residue no-collision "
            f"row, currently {frontier_tuple}, using source-pinned sibling "
            f"seed(s) {frontier_seeds}; keep it finite-window and open-boundary."
        )
    elif frontier_tuple is not None:
        frontier_description = (
            "Start from the first source-unpinned and family-uncovered "
            "power-residue no-collision row, currently "
            f"{frontier_tuple}, and decide whether it has a compact finite "
            "proof hook or reveals an honest boundary."
        )
    else:
        frontier_description = (
            "Widen the positive reconstruction scan until an uncovered "
            "power-residue no-collision row appears."
        )
    tasks = [
        (
            1,
            frontier_task_id,
            frontier_description,
        ),
        (
            2,
            "rank_deeper_positive_reconstruction_candidates",
            "Add a focused candidate surface only if the program atlas needs more reconstruction-specific fields.",
        ),
        (
            3,
            "return_to_family_arithmetic_when_signal_warrants",
            "Classify Shape187 or Shape13 arithmetic only when the atlas exposes stronger family signal than the reconstruction lane.",
        ),
    ]
    return [
        {
            "group": OBSERVABILITY_PROGRAM_NEXT_TASK_GROUP,
            "program_next_task_rank": rank,
            "program_next_task_id": task_id,
            "program_next_task": description,
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            "observability_boundary_status": (
                "empirical_open_boundary_program_guidance"
            ),
        }
        for rank, task_id, description in tasks
    ]


def _target_signature_rows_from_atlas(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    atlas_case_rows: Sequence[dict[str, Any]],
    top: int,
) -> list[dict[str, Any]]:
    by_signature: dict[str, list[dict[str, Any]]] = {}
    for row in atlas_case_rows:
        by_signature.setdefault(
            str(row["observability_target_summary_signature"]), []
        ).append(row)
    family_rows = [
        _observability_target_signature_family_row(
            signature_rank=0,
            signature=signature,
            members=sorted(members, key=_observability_sort_key),
        )
        for signature, members in by_signature.items()
    ]
    family_rows.sort(key=_observability_target_signature_sort_key)
    for rank, row in enumerate(family_rows, start=1):
        row["signature_rank"] = rank
    emitted_rows = family_rows[:top] if top and top > 0 else list(family_rows)
    return [
        _observability_target_signature_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            all_families=family_rows,
            emitted_families=emitted_rows,
        ),
        *emitted_rows,
    ]


def _instrument_rows_from_atlas(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    atlas_case_rows: Sequence[dict[str, Any]],
    top: int,
) -> list[dict[str, Any]]:
    conflict_rows = [
        row
        for row in atlas_case_rows
        if row.get("coefficient_observability_class")
        in {"hidden_coefficient_conflict", "visible_coefficient_conflict"}
    ]
    hidden_keys = {
        _source_symmetry_key(row)
        for row in conflict_rows
        if row["coefficient_observability_class"] == "hidden_coefficient_conflict"
    }
    grouped: dict[tuple[int, int, int], list[dict[str, Any]]] = {
        key: [] for key in hidden_keys
    }
    for row in conflict_rows:
        key = _source_symmetry_key(row)
        if key in grouped:
            grouped[key].append(row)

    shape_pairs: list[tuple[dict[str, Any], list[dict[str, Any]]]] = []
    for key, members in grouped.items():
        members.sort(key=_observability_sort_key)
        shape_pairs.append(
            (_source_shape_row(key=key, members=members, rank=0), members)
        )
    shape_pairs.sort(key=lambda pair: _source_shape_sort_key(pair[0]))
    all_shape_rows = [shape for shape, _ in shape_pairs]
    if top and top > 0:
        shape_pairs = shape_pairs[:top]
    for rank, (shape, _) in enumerate(shape_pairs, start=1):
        shape["shape_rank"] = rank

    emitted_rows: list[dict[str, Any]] = []
    emitted_member_count = 0
    for shape, members in shape_pairs:
        emitted_rows.append(shape)
        member_rows = _source_shape_member_rows(shape_row=shape, members=members)
        emitted_member_count += len(member_rows)
        emitted_rows.extend(member_rows)
    return [
        _observability_instrument_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            all_shapes=all_shape_rows,
            emitted_shapes=[shape for shape, _ in shape_pairs],
            emitted_member_count=emitted_member_count,
        ),
        *emitted_rows,
    ]


def _shape17_rows_from_instrument(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    instrument_rows: Sequence[dict[str, Any]],
    top: int,
) -> list[dict[str, Any]]:
    members = [
        row
        for row in instrument_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature")
        == SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    for row in members:
        exported = dict(row)
        same_core_multiplier = (
            int(row["n"]) // 17 if int(row["n"]) % 17 == 0 else None
        )
        positions = list(row.get("conflict_positions") or [])
        canonical_positions = list(row.get("canonical_conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE17_K4_MEMBER_GROUP,
                "family_class": "first_emitted_shape17_k4_position_gap_four",
                "source_symmetry_family_role": _shape17_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "shape17_family_bridge_note": _shape17_family_bridge_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_shape17_k4_family_classifier"
                ),
                "next_observability_task": (
                    "prove_or_reject_shape17_same_core_shift_pattern"
                ),
                **_shape17_same_core_shift_fields(
                    row,
                    same_core_multiplier=same_core_multiplier,
                    local_scale=local_scale,
                ),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_shape17_member_sort_key)
    emitted_members = classified_members[:top] if top and top > 0 else classified_members
    return [
        _shape17_family_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _shape13_rows_from_atlas(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    atlas_case_rows: Sequence[dict[str, Any]],
    top: int,
) -> list[dict[str, Any]]:
    mod_stable_rows = [
        row for row in atlas_case_rows if _is_mod_stable_carry_loss_row(row)
    ]
    mod_stable_rows.sort(key=_mod_stable_carry_loss_sort_key)
    mod_stable_cases = [
        _mod_stable_carry_loss_case_row(row, rank)
        for rank, row in enumerate(mod_stable_rows, start=1)
    ]
    base_members = [
        row
        for row in mod_stable_cases
        if row.get("source_symmetry_signature")
        == SHAPE13_K4_MOD_STABLE_SOURCE_SYMMETRY_SIGNATURE
    ]
    core_row = next(
        (
            row
            for row in base_members
            if int(row["n"]) == int(row["periodic_modulus"])
        ),
        None,
    )
    classified_members: list[dict[str, Any]] = []
    for row in sorted(base_members, key=_shape13_k4_member_sort_key):
        shape13_fields = _shape13_k4_member_fields(row, core_row=core_row)
        exported = dict(row)
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE13_K4_MOD_STABLE_CARRY_LOSS_MEMBER_GROUP,
                "family_class": "shape13_k4_mod_stable_carry_loss_shift",
                "observability_boundary_status": (
                    "empirical_open_boundary_shape13_k4_mod_stable_carry_loss_classifier"
                ),
                "next_observability_task": shape13_fields["shape13_k4_next_lean_task"],
                **shape13_fields,
            }
        )
        classified_members.append(exported)
    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank
    emitted_members = classified_members[:top] if top and top > 0 else classified_members
    return [
        _shape13_k4_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _next_source_shape_rows_from_instrument(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    instrument_rows: Sequence[dict[str, Any]],
    top: int,
    skipped_signatures: Sequence[str],
) -> list[dict[str, Any]]:
    skipped = tuple(skipped_signatures)
    shape_rows = [
        row
        for row in instrument_rows
        if row.get("group") == OBSERVABILITY_SOURCE_SHAPE_GROUP
    ]
    selected_shape = next(
        (
            row
            for row in shape_rows
            if str(row.get("source_symmetry_signature")) not in skipped
        ),
        None,
    )
    selected_signature = (
        str(selected_shape["source_symmetry_signature"]) if selected_shape else None
    )
    members = [
        row
        for row in instrument_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature") == selected_signature
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    canonical_positions = (
        list(selected_shape.get("canonical_conflict_positions", []))
        if selected_shape
        else []
    )
    for row in members:
        exported = dict(row)
        positions = list(row.get("conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        periodic_modulus = int(row["periodic_modulus"])
        same_core_multiplier = (
            int(row["n"]) // periodic_modulus
            if int(row["n"]) % periodic_modulus == 0
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_NEXT_SOURCE_SHAPE_MEMBER_GROUP,
                "family_class": "next_unresolved_source_shape_family",
                "source_shape_selection_reason": (
                    "first_unsettled_after_skipped_signatures"
                ),
                "skipped_source_symmetry_signatures": list(skipped),
                "instrument_shape_rank": row.get("shape_rank"),
                "instrument_member_rank": row.get("member_rank"),
                "selected_shape_rank": (
                    selected_shape.get("shape_rank") if selected_shape else None
                ),
                "source_symmetry_family_role": _generic_source_shape_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "next_source_shape_family_note": _generic_source_shape_family_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_next_source_shape_family_classifier"
                ),
                "next_observability_task": (
                    "classify_next_source_shape_family_or_add_finite_package"
                ),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_next_source_shape_member_sort_key)
    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank
    emitted_members = classified_members[:top] if top and top > 0 else classified_members
    return [
        _next_source_shape_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            skipped_signatures=skipped,
            selected_shape=selected_shape,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _shape187_rows_from_instrument(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    instrument_rows: Sequence[dict[str, Any]],
    top: int,
) -> list[dict[str, Any]]:
    members = [
        row
        for row in instrument_rows
        if row.get("group") == OBSERVABILITY_INSTRUMENT_MEMBER_GROUP
        and row.get("source_symmetry_signature")
        == SHAPE187_K188_SOURCE_SYMMETRY_SIGNATURE
    ]
    minima_by_base = _base_local_coefficient_scales(members)
    classified_members: list[dict[str, Any]] = []
    for row in members:
        exported = dict(row)
        same_core_multiplier = (
            int(row["n"]) // 187 if int(row["n"]) % 187 == 0 else None
        )
        positions = list(row.get("conflict_positions") or [])
        canonical_positions = list(row.get("canonical_conflict_positions") or [])
        position_shift = (
            int(positions[0]) - int(canonical_positions[0])
            if positions and canonical_positions
            else None
        )
        coefficients = list(row.get("conflict_coefficients") or [])
        min_coefficient = minima_by_base.get(int(row["base"]))
        local_scale = None
        if coefficients and min_coefficient:
            first_coefficient = int(coefficients[0])
            if first_coefficient % min_coefficient == 0:
                local_scale = first_coefficient // min_coefficient
        exported.update(
            {
                "group": OBSERVABILITY_SHAPE187_K188_MEMBER_GROUP,
                "family_class": "shape187_k188_same_position_scaling",
                "source_symmetry_family_role": _shape187_family_role(row),
                "same_core_multiplier": same_core_multiplier,
                "position_shift_from_canonical": position_shift,
                "base_local_min_first_coefficient": min_coefficient,
                "base_local_coefficient_scale": local_scale,
                "shape187_family_bridge_note": _shape187_family_bridge_note(row),
                "observability_boundary_status": (
                    "empirical_open_boundary_shape187_k188_family_classifier"
                ),
                "next_observability_task": (
                    "extend_same_position_idempotent_criterion_to_remaining_shape187_rows_or_add_next_finite_package"
                ),
                **_shape187_same_position_scaling_fields(row),
            }
        )
        classified_members.append(exported)
    classified_members.sort(key=_shape187_member_sort_key)
    for family_member_rank, row in enumerate(classified_members, start=1):
        row["family_member_rank"] = family_member_rank
    emitted_members = classified_members[:top] if top and top > 0 else classified_members
    return [
        _shape187_family_summary_row(
            bases=bases,
            max_n=max_n,
            requested_blocks=requested_blocks,
            all_members=classified_members,
            emitted_members=emitted_members,
        ),
        *emitted_members,
    ]


def _program_summary_row(
    *,
    bases: tuple[int, ...],
    max_n: int,
    requested_blocks: int,
    atlas_summary: Mapping[str, Any],
    target_signature_summary: Mapping[str, Any],
    instrument_summary: Mapping[str, Any],
    positive_candidates: Sequence[dict[str, Any]],
    family_rows: Sequence[dict[str, Any]],
    lane_rows: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    first_tuple = (
        _tuple_from_observability_row(positive_candidates[0])
        if positive_candidates
        else None
    )
    source_pinned_positive = [
        row
        for row in positive_candidates
        if row.get("positive_reconstruction_source_pinned") is True
    ]
    source_pinned_tuples = [
        _tuple_from_observability_row(row) for row in source_pinned_positive
    ]
    source_pinned_theorems = [
        row["positive_reconstruction_qualified_theorem_names"][-1]
        for row in source_pinned_positive
        if row.get("positive_reconstruction_qualified_theorem_names")
    ]
    injective_criterion_rows = [
        row
        for row in positive_candidates
        if row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
    ]
    power_no_collision_rows = [
        row
        for row in positive_candidates
        if row.get(
            "positive_reconstruction_hyp_remainder_power_residue_window_injective"
        )
        is True
    ]
    power_no_wrap_rows = [
        row
        for row in positive_candidates
        if row.get("positive_reconstruction_hyp_remainder_power_residue_no_wrap")
        is True
    ]
    frontier_decision_fields = _positive_reconstruction_frontier_decision_fields(
        positive_candidates
    )
    return {
        "group": OBSERVABILITY_PROGRAM_SUMMARY_GROUP,
        "bases": list(bases),
        "requested_blocks": requested_blocks,
        "max_n": max_n,
        "target_signature_family_count": int(
            target_signature_summary.get("total_signature_families", 0)
        ),
        "hidden_source_shape_count": int(
            instrument_summary.get("total_shapes", 0)
        ),
        "cross_base_shape_count": int(
            instrument_summary.get("cross_base_shape_count", 0)
        ),
        "lean_ready_hidden_conflicts": int(
            atlas_summary.get("lean_ready_hidden_conflict_cases", 0)
        ),
        "positive_functional_frontier_count": int(
            atlas_summary.get("coefficient_functional_frontier_cases", 0)
        ),
        "emitted_positive_reconstruction_candidates": len(positive_candidates),
        "source_pinned_positive_reconstruction_cases": len(source_pinned_positive),
        "empirical_positive_reconstruction_candidates": (
            len(positive_candidates) - len(source_pinned_positive)
        ),
        "source_pinned_positive_reconstruction_tuples": source_pinned_tuples,
        "source_pinned_positive_reconstruction_theorems": source_pinned_theorems,
        "positive_reconstruction_arithmetic_criterion_id": (
            POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_ID
        ),
        "positive_reconstruction_arithmetic_criterion_formula": (
            POSITIVE_RECONSTRUCTION_INJECTIVE_WINDOW_CRITERION_FORMULA
        ),
        "positive_reconstruction_injective_window_criterion_cases": len(
            injective_criterion_rows
        ),
        "source_pinned_positive_reconstruction_injective_window_cases": sum(
            1
            for row in injective_criterion_rows
            if row.get("positive_reconstruction_source_pinned") is True
        ),
        "positive_reconstruction_power_no_collision_criterion_id": (
            POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_ID
        ),
        "positive_reconstruction_power_no_collision_criterion_formula": (
            POSITIVE_RECONSTRUCTION_POWER_NO_COLLISION_CRITERION_FORMULA
        ),
        "positive_reconstruction_power_no_collision_criterion_cases": len(
            power_no_collision_rows
        ),
        "source_pinned_positive_reconstruction_power_no_collision_cases": sum(
            1
            for row in power_no_collision_rows
            if row.get("positive_reconstruction_source_pinned") is True
        ),
        "positive_reconstruction_power_no_wrap_criterion_id": (
            POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_ID
        ),
        "positive_reconstruction_power_no_wrap_criterion_formula": (
            POSITIVE_RECONSTRUCTION_POWER_NO_WRAP_CRITERION_FORMULA
        ),
        "positive_reconstruction_power_no_wrap_criterion_cases": len(
            power_no_wrap_rows
        ),
        "source_pinned_positive_reconstruction_power_no_wrap_cases": sum(
            1
            for row in power_no_wrap_rows
            if row.get("positive_reconstruction_source_pinned") is True
        ),
        "emitted_program_lanes": len(lane_rows),
        "emitted_program_families": len(family_rows),
        "first_positive_reconstruction_tuple": first_tuple,
        "recommended_next_observability_task": (
            frontier_decision_fields["recommended_positive_reconstruction_next_task"]
        ),
        **frontier_decision_fields,
        "observability_boundary_status": (
            "empirical_open_boundary_program_atlas_tooling"
        ),
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
    }


def observability_program_atlas_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 50,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Coordinate observability evidence lanes without adding new arithmetic."""

    parsed_bases = _parse_bases(bases)
    atlas_rows = observability_atlas_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    atlas_summary = atlas_rows[0]
    atlas_case_rows = [
        row for row in atlas_rows if row.get("group") != OBSERVABILITY_SUMMARY_GROUP
    ]
    target_signature_rows = _target_signature_rows_from_atlas(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        atlas_case_rows=atlas_case_rows,
        top=0,
    )
    target_signature_summary = target_signature_rows[0]
    functional_signature = next(
        (
            row
            for row in target_signature_rows
            if row.get("signature_family_class")
            == "all_pointwise_targets_functional_frontier"
        ),
        None,
    )
    instrument_rows = _instrument_rows_from_atlas(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        atlas_case_rows=atlas_case_rows,
        top=0,
    )
    instrument_summary = instrument_rows[0]
    shape17_rows = _shape17_rows_from_instrument(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        instrument_rows=instrument_rows,
        top=0,
    )
    shape17_summary = shape17_rows[0] if shape17_rows else None
    shape187_rows = _shape187_rows_from_instrument(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        instrument_rows=instrument_rows,
        top=0,
    )
    shape187_summary = shape187_rows[0] if shape187_rows else None
    shape13_rows = _shape13_rows_from_atlas(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        atlas_case_rows=atlas_case_rows,
        top=0,
    )
    shape13_summary = shape13_rows[0] if shape13_rows else None
    unresolved_rows = _next_source_shape_rows_from_instrument(
        bases=parsed_bases,
        max_n=max_n,
        requested_blocks=n_blocks,
        instrument_rows=instrument_rows,
        top=0,
        skipped_signatures=(
            SHAPE17_K4_SOURCE_SYMMETRY_SIGNATURE,
            SHAPE187_K188_SOURCE_SYMMETRY_SIGNATURE,
        ),
    )
    unresolved_summary = unresolved_rows[0] if unresolved_rows else None

    positive_all = sorted(
        [
            row
            for row in atlas_case_rows
            if _is_positive_reconstruction_candidate(row)
        ],
        key=_positive_reconstruction_sort_key,
    )
    positive_all_rows = [
        _positive_reconstruction_candidate_row(row, rank)
        for rank, row in enumerate(positive_all, start=1)
    ]
    frontier_anchor_fields = _positive_reconstruction_frontier_decision_fields(
        positive_all_rows
    )
    dynamic_positive_anchors: list[tuple[int, int]] = [(10, 98), (10, 97), (10, 996)]
    first_uncovered_tuple = frontier_anchor_fields.get(
        "first_uncovered_positive_reconstruction_tuple"
    )
    if first_uncovered_tuple:
        dynamic_positive_anchors.append(
            (int(first_uncovered_tuple[0]), int(first_uncovered_tuple[1]))
        )
    positive_selected = _select_with_anchors(
        positive_all_rows,
        top,
        anchors=dynamic_positive_anchors,
    )
    positive_rows = list(positive_selected)

    family_rows = [
        _program_family_row(
            lane_rank=1,
            family_id="shape17_k4_composite68_proof_backed_obstruction",
            lane_id="composite68_shape17_obstruction_lane",
            summary=shape17_summary,
            family_label="Composite68 / Shape17 proof-backed obstruction family",
            support_status="proof_backed_hidden_output_obstruction_family",
            next_task="use_shape17_as_obstruction_flagship_baseline",
        ),
        _program_family_row(
            lane_rank=2,
            family_id="shape187_k188_same_position_scaling",
            lane_id="shape187_same_position_scaling_lane",
            summary=shape187_summary,
            family_label="Shape187/K188 same-position scaling family",
            support_status="partially_proof_backed_same_position_scaling_family",
            next_task="finish_or_bound_shape187_same_position_scaling_candidates",
        ),
        _program_family_row(
            lane_rank=3,
            family_id="shape13_k4_mod_stable_carry_loss",
            lane_id="shape13_mod_stable_carry_loss_lane",
            summary=shape13_summary,
            family_label="Shape13/K4 mod-stable carry-loss family",
            support_status="proof_backed_target_split_loss_seed_family",
            next_task="wait_for_new_shape13_scale_two_candidate_or_widen_scan",
        ),
        _program_family_row(
            lane_rank=4,
            family_id="unresolved_hidden_conflict_source_family",
            lane_id="unresolved_hidden_conflict_lane",
            summary=unresolved_summary,
            family_label="First unresolved hidden-conflict family after settled lanes",
            support_status="finite_only_hidden_conflict_family",
            next_task="defer_until_obstruction_signal_outweighs_reconstruction_signal",
        ),
        _program_family_row(
            lane_rank=5,
            family_id="positive_functional_frontier_signature_family",
            lane_id="positive_reconstruction_lane",
            summary=functional_signature,
            family_label="Positive reconstruction functional-frontier family",
            support_status="empirical_factor_through_candidate_family",
            next_task="prove_first_positive_reconstruction_exemplar",
        ),
    ]
    lane_rows = _program_lane_rows(
        shape17_summary=shape17_summary,
        shape187_summary=shape187_summary,
        shape13_summary=shape13_summary,
        unresolved_summary=unresolved_summary,
        positive_candidates=positive_rows,
    )
    next_task_rows = _program_next_task_rows(positive_rows)
    return [
        _program_summary_row(
            bases=parsed_bases,
            max_n=max_n,
            requested_blocks=n_blocks,
            atlas_summary=atlas_summary,
            target_signature_summary=target_signature_summary,
            instrument_summary=instrument_summary,
            positive_candidates=positive_rows,
            family_rows=family_rows,
            lane_rows=lane_rows,
        ),
        *lane_rows,
        *family_rows,
        *positive_rows,
        *next_task_rows,
    ]


def _lean_fixture_row(row: Mapping[str, Any]) -> dict[str, Any] | None:
    anchor = LEAN_FIXTURE_ANCHORS.get((int(row["base"]), int(row["n"])))
    if anchor is None:
        return None
    if row["certificate_class"] != "lean_ready_hidden_conflict":
        return None
    if row["lean_readiness"] != "existing_composite68_family_theorem":
        return None
    namespace = str(anchor["namespace"])
    theorem_names = list(LEAN_FIXTURE_THEOREM_NAMES)
    copyable_lean_stub = _copyable_lean_stub_for_row(row)
    fixture = {
        "certificate_id": row["certificate_id"],
        "namespace": namespace,
        "module_path": anchor["module_path"],
        "fixture_status": SOURCE_PINNED_FIXTURE_STATUS,
        "theorem_names": theorem_names,
        "qualified_theorem_names": [
            f"{namespace}.{theorem_name}" for theorem_name in theorem_names
        ],
        "proof_path_snippet": LEAN_FIXTURE_PROOF_PATH_SNIPPET,
        "copyable_lean_stub": copyable_lean_stub,
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
        "certificate_class": row["certificate_class"],
        "lean_readiness": row["lean_readiness"],
        "next_lean_task": row["next_lean_task"],
        "base": row["base"],
        "n": row["n"],
        "periodic_modulus": row["periodic_modulus"],
        "m": row["m"],
        "B": row["B"],
        "q": row["q"],
        "k": row["k"],
        "requested_blocks": row["requested_blocks"],
        "certified_lookahead_blocks": row["certified_lookahead_blocks"],
        "exact_gap_numerator": row["exact_gap_numerator"],
        "conflict_remainder_state": row["conflict_remainder_state"],
        "conflict_positions": row["conflict_positions"],
        "conflict_coefficients": row["conflict_coefficients"],
        "conflict_carry_states": row["conflict_carry_states"],
        "conflict_block_values": row["conflict_block_values"],
        "conflict_output_hidden": row["conflict_output_hidden"],
        "conflict_position_gap": row["conflict_position_gap"],
        "conflict_coefficient_delta": row["conflict_coefficient_delta"],
    }
    fixture["certificate_tuple"] = [
        int(fixture["base"]),
        int(fixture["n"]),
        int(fixture["m"]),
        int(fixture["B"]),
        int(fixture["q"]),
        int(fixture["k"]),
        int(fixture["certified_lookahead_blocks"]),
        int(fixture["exact_gap_numerator"]),
    ]
    return fixture


_NAT_THEOREM_TOKENS = {
    0: "zero",
    1: "one",
    2: "two",
    3: "three",
    4: "four",
    5: "five",
    6: "six",
    7: "seven",
    8: "eight",
    9: "nine",
    10: "ten",
    11: "eleven",
    12: "twelve",
    13: "thirteen",
    14: "fourteen",
    15: "fifteen",
    16: "sixteen",
    17: "seventeen",
    18: "eighteen",
    19: "nineteen",
    20: "twenty",
}


def _nat_theorem_token(value: Any) -> str:
    as_int = int(value)
    return _NAT_THEOREM_TOKENS.get(as_int, str(as_int))


def _scaffold_record_theorem_name(row: Mapping[str, Any]) -> str:
    positions = list(row.get("conflict_positions") or [])
    if len(positions) != 2:
        return DEFAULT_FIXTURE_RECORD_THEOREM_NAME
    left, right = (_nat_theorem_token(position) for position in positions)
    requested = _nat_theorem_token(row["requested_blocks"])
    lookahead = _nat_theorem_token(row["certified_lookahead_blocks"])
    return (
        f"coordinate_stateAlignments_{left}_{right}_certifiedConflict_"
        f"{requested}_{lookahead}"
    )


def _scaffold_projection_theorem_name(row: Mapping[str, Any]) -> str:
    requested = _nat_theorem_token(row["requested_blocks"])
    lookahead = _nat_theorem_token(row["certified_lookahead_blocks"])
    return (
        "coordinate_obstructionRecord_proofPath_"
        f"not_remainderToCoefficientFunctional_{requested}_{lookahead}"
    )


def _fixture_theorem_names_for_row(row: Mapping[str, Any] | None) -> list[str]:
    if row is None:
        return list(LEAN_FIXTURE_THEOREM_NAMES)
    if (int(row["base"]), int(row["n"])) in LEAN_FIXTURE_ANCHORS:
        return list(LEAN_FIXTURE_THEOREM_NAMES)
    if row.get("conflict_remainder_state") is not None:
        return [
            _scaffold_record_theorem_name(row),
            _scaffold_projection_theorem_name(row),
            f"{row['certificate_id']}_not_remainderToCoefficientFunctional",
        ]
    return list(LEAN_FIXTURE_THEOREM_NAMES)


def _fixture_record_theorem_name_for_row(row: Mapping[str, Any] | None) -> str:
    return _fixture_theorem_names_for_row(row)[0]


def _copyable_lean_stub_for_row(
    row: Mapping[str, Any],
    *,
    record_theorem_name: str | None = None,
    projection_accessor: str = DEFAULT_FIXTURE_PROJECTION_ACCESSOR,
) -> dict[str, Any]:
    if record_theorem_name is None:
        record_theorem_name = _fixture_record_theorem_name_for_row(row)
    requested_blocks = int(row["requested_blocks"])
    certified_lookahead_blocks = int(row["certified_lookahead_blocks"])
    stub_theorem_name = (
        f"{row['certificate_id']}_not_remainderToCoefficientFunctional"
    )
    return {
        "kind": "not_remainder_to_coefficient_functional_projection",
        "recommended_theorem_name": stub_theorem_name,
        "record_theorem_name": record_theorem_name,
        "projection_accessor": projection_accessor,
        "code": (
            "/-- Copyable fixture stub generated from certificate-lean-fixtures-v1. -/\n"
            f"theorem {stub_theorem_name} :\n"
            "    ¬ List.FunctionalOnFst\n"
            "      ((coordinate.stateAlignments "
            f"coordinate_goodMode {requested_blocks} {certified_lookahead_blocks}).map\n"
            "        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by\n"
            f"  have hrecord := {record_theorem_name}\n"
            f"  exact hrecord.{projection_accessor}"
        ),
    }


def certificate_lean_fixture_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Return source-pinned Lean fixture rows from Lean-ready certificates."""

    workbench_rows = certificate_workbench_rows(
        max_n=max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=top,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    fixture_rows = [
        fixture
        for row in workbench_rows
        if row.get("group") == WORKBENCH_CASE_GROUP
        for fixture in [_lean_fixture_row(row)]
        if fixture is not None
    ]
    fixture_rows.sort(
        key=lambda row: (
            int(row["base"]) != 10,
            int(row["exact_gap_numerator"]),
            int(row["base"]),
            int(row["n"]),
        )
    )
    return fixture_rows


def certificate_lean_fixture_payload(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> dict[str, Any]:
    """Return the JSON payload for source-pinned Certificate-to-Lean fixtures."""

    parsed_bases = _parse_bases(bases)
    fixtures = certificate_lean_fixture_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=top,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    first_tuple = fixtures[0]["certificate_tuple"] if fixtures else None
    return {
        "schema": CERTIFICATE_LEAN_FIXTURE_SCHEMA,
        "summary": {
            "source_surface": "visibility-certificate-workbench",
            "max_n": max_n,
            "bases": list(parsed_bases),
            "requested_blocks": n_blocks,
            "emitted_fixture_count": len(fixtures),
            "namespaces": [fixture["namespace"] for fixture in fixtures],
            "first_tuple": first_tuple,
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            "fixture_status": SOURCE_PINNED_FIXTURE_STATUS,
        },
        "fixtures": fixtures,
    }


def _lint_copyable_lean_stub(fixture: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    stub = fixture.get("copyable_lean_stub")
    if not isinstance(stub, Mapping):
        return ["missing copyable_lean_stub"]

    expected_theorem_name = (
        f"{fixture['certificate_id']}_not_remainderToCoefficientFunctional"
    )
    if stub.get("kind") != "not_remainder_to_coefficient_functional_projection":
        errors.append("unexpected stub kind")
    if stub.get("recommended_theorem_name") != expected_theorem_name:
        errors.append("recommended theorem name does not match certificate id")
    if stub.get("record_theorem_name") not in fixture.get("theorem_names", []):
        errors.append("record theorem name is not pinned by fixture")
    if stub.get("projection_accessor") != DEFAULT_FIXTURE_PROJECTION_ACCESSOR:
        errors.append("unexpected projection accessor")

    code = stub.get("code")
    if not isinstance(code, str):
        errors.append("missing Lean code")
        return errors
    if f"theorem {expected_theorem_name} :" not in code:
        errors.append("Lean code does not declare the recommended theorem")
    record_theorem_name = stub.get("record_theorem_name")
    if isinstance(record_theorem_name, str) and record_theorem_name not in code:
        errors.append("Lean code does not cite the pinned record theorem")
    projection_accessor = stub.get("projection_accessor")
    if isinstance(projection_accessor, str) and f".{projection_accessor}" not in code:
        errors.append("Lean code does not use the projection accessor")
    return errors


def _dedupe_bases_with_candidate(
    bases: Iterable[int], candidate_base: int
) -> tuple[int, ...]:
    parsed: list[int] = []
    for base in [*bases, candidate_base]:
        value = int(base)
        if value not in parsed:
            parsed.append(value)
    return _parse_bases(parsed)


def _certificate_tuple_from_row(row: Mapping[str, Any]) -> list[int]:
    return [
        int(row["base"]),
        int(row["n"]),
        int(row["m"]),
        int(row["B"]),
        int(row["q"]),
        int(row["k"]),
        int(row["certified_lookahead_blocks"]),
        int(row["exact_gap_numerator"]),
    ]


def _workbench_case_for_candidate(
    *,
    candidate_base: int,
    candidate_n: int,
    candidate_m: int | None,
    max_n: int,
    bases: tuple[int, ...],
    n_blocks: int,
    max_lookahead_blocks: int,
) -> dict[str, Any] | None:
    rows = certificate_workbench_rows(
        max_n=max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    for row in rows:
        if row.get("group") != WORKBENCH_CASE_GROUP:
            continue
        if int(row["base"]) != int(candidate_base):
            continue
        if int(row["n"]) != int(candidate_n):
            continue
        if candidate_m is not None and int(row["m"]) != int(candidate_m):
            continue
        return row
    return None


def _lean_declaration_names_from_text(text: str) -> set[str]:
    pattern = re.compile(
        r"^(?:@\[[^\n]+\]\s*)?"
        r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
        r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)",
        re.MULTILINE,
    )
    return {match.group(1) for match in pattern.finditer(text)}


def _lean_namespace_block(text: str, namespace: str) -> tuple[str, bool]:
    namespace_pattern = re.compile(
        rf"^[ \t]*namespace[ \t]+{re.escape(namespace)}(?:[ \t]*$|[ \t])",
        re.MULTILINE,
    )
    namespace_match = namespace_pattern.search(text)
    if namespace_match is None:
        return "", False
    after_namespace = text[namespace_match.end() :]
    end_pattern = re.compile(
        rf"^[ \t]*end[ \t]+{re.escape(namespace)}(?:[ \t]*$|[ \t])",
        re.MULTILINE,
    )
    end_match = end_pattern.search(after_namespace)
    if end_match is None:
        return after_namespace, False
    return after_namespace[: end_match.start()], True


def _lean_source_mapping_checks(
    *,
    namespace: str,
    module_path: str,
    theorem_guide_path: str,
    required_theorem_names: Sequence[str],
) -> dict[str, Any]:
    module = Path(module_path)
    module_text = module.read_text() if module.exists() else ""
    namespace_block, namespace_found = (
        _lean_namespace_block(module_text, namespace) if module_text else ("", False)
    )
    declarations = _lean_declaration_names_from_text(namespace_block)
    missing_source_theorem_names = [
        theorem_name
        for theorem_name in required_theorem_names
        if theorem_name not in declarations
    ]

    theorem_guide = Path(theorem_guide_path)
    theorem_guide_text = theorem_guide.read_text() if theorem_guide.exists() else ""
    qualified_names = [
        f"{namespace}.{theorem_name}" for theorem_name in required_theorem_names
    ]
    missing_theorem_guide_mentions = [
        qualified_name
        for qualified_name in qualified_names
        if qualified_name not in theorem_guide_text
    ]
    return {
        "module_path_exists": module.exists(),
        "namespace_found": namespace_found,
        "theorem_guide_path_exists": theorem_guide.exists(),
        "required_theorem_names": list(required_theorem_names),
        "qualified_theorem_names": qualified_names,
        "missing_source_theorem_names": missing_source_theorem_names,
        "missing_theorem_guide_mentions": missing_theorem_guide_mentions,
    }


def _source_pinning_recipe(
    *,
    namespace: str,
    module_path: str,
    theorem_guide_path: str,
    required_theorem_names: Sequence[str],
    copyable_lean_stub: Mapping[str, Any] | None,
) -> dict[str, Any]:
    stub_theorem_name = (
        copyable_lean_stub.get("recommended_theorem_name")
        if isinstance(copyable_lean_stub, Mapping)
        else None
    )
    record_theorem_name = (
        str(copyable_lean_stub.get("record_theorem_name"))
        if isinstance(copyable_lean_stub, Mapping)
        else (
            str(required_theorem_names[0])
            if required_theorem_names
            else DEFAULT_FIXTURE_RECORD_THEOREM_NAME
        )
    )
    return {
        "recipe_id": SOURCE_PINNING_RECIPE_ID,
        "recipe_role": "candidate_mapping_recipe",
        "candidate_mapping_goal": (
            "turn a scaffold-ready workbench certificate into an intentional "
            "source-pinned fixture mapping"
        ),
        "status_transition": [
            "scaffold_ready_pending_lean_source",
            "source_ready_existing_mapping",
        ],
        "steps": [
            f"Add or confirm namespace {namespace} in {module_path}.",
            (
                "Prove or expose the required theorem names, starting with "
                f"{record_theorem_name} as the record theorem."
            ),
            (
                "Add theorem-guide mentions for each qualified theorem name "
                f"in {theorem_guide_path}."
            ),
            (
                "Use proposed_mapping.copyable_lean_stub.code as the projection "
                "exemplar while the package remains scaffold-only."
            ),
            (
                "Rerun the mapping lint command and add a source-pinned fixture "
                "anchor only after it reports source_ready_existing_mapping."
            ),
        ],
        "required_theorem_names": list(required_theorem_names),
        "record_theorem_name": record_theorem_name,
        "projection_accessor": DEFAULT_FIXTURE_PROJECTION_ACCESSOR,
        "copyable_stub_theorem_name": stub_theorem_name,
        "copyable_stub_field": "proposed_mapping.copyable_lean_stub.code",
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
        "promotion_boundary": (
            "No registry IDs, theorem-witness promotion, atlas status change, "
            "or Lean theorem-surface claim is created by this recipe."
        ),
    }


def _default_scaffold_namespace(
    row: Mapping[str, Any],
    namespace_prefix: str = DEFAULT_SCAFFOLD_NAMESPACE_PREFIX,
) -> str:
    return f"{namespace_prefix}Base{int(row['base'])}N{int(row['n'])}"


def _lean_package_plan(
    *,
    row: Mapping[str, Any],
    namespace: str,
    module_path: str,
    theorem_guide_path: str,
    required_theorem_names: Sequence[str],
    copyable_lean_stub: Mapping[str, Any] | None,
) -> dict[str, Any]:
    needs_finite_package = row.get("lean_readiness") == "needs_finite_example_package"
    hidden_conflict = bool(row.get("conflict_output_hidden"))
    worth_proving_next = needs_finite_package and hidden_conflict
    if worth_proving_next:
        decision = "prove_next_finite_obstruction_example"
        decision_reason = (
            "first scaffold-ready hidden-output conflict after source-pinned "
            "Composite68 anchors; small N=7 package can test the non-Composite68 "
            "finite obstruction path"
        )
    elif row.get("lean_readiness") == "existing_composite68_family_theorem":
        decision = "skip_existing_source_pinned_anchor"
        decision_reason = (
            "this certificate is already covered by the existing Composite68 "
            "source-pinned theorem surface"
        )
    else:
        decision = "defer_until_stronger_signal"
        decision_reason = (
            "the candidate is not currently a hidden-conflict finite package "
            "target under the workbench classifier"
        )

    stub_theorem_name = (
        copyable_lean_stub.get("recommended_theorem_name")
        if isinstance(copyable_lean_stub, Mapping)
        else None
    )
    record_theorem_name = (
        str(copyable_lean_stub.get("record_theorem_name"))
        if isinstance(copyable_lean_stub, Mapping)
        else (
            str(required_theorem_names[0])
            if required_theorem_names
            else DEFAULT_FIXTURE_RECORD_THEOREM_NAME
        )
    )
    return {
        "plan_id": LEAN_FINITE_PACKAGE_PLAN_ID,
        "candidate_id": row["certificate_id"],
        "candidate_tuple": _certificate_tuple_from_row(row),
        "recommended_namespace": namespace,
        "module_path": module_path,
        "theorem_guide_path": theorem_guide_path,
        "worth_proving_next": worth_proving_next,
        "decision": decision,
        "decision_reason": decision_reason,
        "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
        "boundary_note": (
            "finite example package only; no registry IDs, theorem-witness "
            "promotion, atlas status change, or global factorization claim"
        ),
        "conflict_shape": {
            "conflict_remainder_state": row.get("conflict_remainder_state"),
            "conflict_positions": row.get("conflict_positions"),
            "conflict_coefficients": row.get("conflict_coefficients"),
            "conflict_carry_states": row.get("conflict_carry_states"),
            "conflict_block_values": row.get("conflict_block_values"),
            "conflict_output_hidden": row.get("conflict_output_hidden"),
            "conflict_position_gap": row.get("conflict_position_gap"),
            "conflict_coefficient_delta": row.get("conflict_coefficient_delta"),
        },
        "required_theorem_names": list(required_theorem_names),
        "record_theorem_name": record_theorem_name,
        "stub_theorem_name": stub_theorem_name,
        "stub_source_field": "proposed_mapping.copyable_lean_stub.code",
        "checklist": [
            f"Add namespace {namespace} in {module_path}.",
            (
                "Define the finite coordinate package for "
                f"(base, N, m, B, q, k, L, gap) = {tuple(_certificate_tuple_from_row(row))}."
            ),
            (
                "Expose the required theorem names, starting with "
                f"{record_theorem_name} as the record payload."
            ),
            (
                "Use proposed_mapping.copyable_lean_stub.code as the projection "
                "sanity check for not_remainderToCoefficientFunctional."
            ),
            (
                f"Add qualified theorem-guide mentions under {theorem_guide_path}."
            ),
            (
                "Rerun visibility-certificate-lean-stubs --first-scaffold-only "
                "until this candidate becomes source_ready_existing_mapping."
            ),
        ],
    }


def certificate_fixture_mapping_lint_payload(
    *,
    candidate_base: int,
    candidate_n: int,
    namespace: str,
    module_path: str = "lean/QRTour/Examples.lean",
    theorem_guide_path: str = "lean/THEOREM_GUIDE.md",
    candidate_m: int | None = None,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    max_lookahead_blocks: int = 128,
) -> dict[str, Any]:
    """Lint a proposed workbench-row-to-Lean fixture mapping without promoting it."""

    parsed_bases = _dedupe_bases_with_candidate(bases, int(candidate_base))
    candidate_row = _workbench_case_for_candidate(
        candidate_base=int(candidate_base),
        candidate_n=int(candidate_n),
        candidate_m=candidate_m,
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    required_theorem_names = _fixture_theorem_names_for_row(candidate_row)
    source_checks = _lean_source_mapping_checks(
        namespace=namespace,
        module_path=module_path,
        theorem_guide_path=theorem_guide_path,
        required_theorem_names=required_theorem_names,
    )

    candidate: dict[str, Any] | None = None
    copyable_lean_stub: dict[str, Any] | None = None
    stub_lint_errors: list[str] = []
    conflict_present = False
    if candidate_row is not None:
        conflict_present = candidate_row.get("conflict_remainder_state") is not None
        candidate = {
            "certificate_id": candidate_row["certificate_id"],
            "certificate_tuple": _certificate_tuple_from_row(candidate_row),
            "certificate_class": candidate_row["certificate_class"],
            "lean_readiness": candidate_row["lean_readiness"],
            "theorem_frontier_status": candidate_row["theorem_frontier_status"],
            "next_lean_task": candidate_row["next_lean_task"],
            "conflict_present": conflict_present,
            "conflict_output_hidden": candidate_row["conflict_output_hidden"],
        }
        if conflict_present:
            copyable_lean_stub = _copyable_lean_stub_for_row(candidate_row)
            proposed_fixture = {
                "certificate_id": candidate_row["certificate_id"],
                "theorem_names": required_theorem_names,
                "copyable_lean_stub": copyable_lean_stub,
            }
            stub_lint_errors = _lint_copyable_lean_stub(proposed_fixture)

    lean_package_plan = (
        _lean_package_plan(
            row=candidate_row,
            namespace=namespace,
            module_path=module_path,
            theorem_guide_path=theorem_guide_path,
            required_theorem_names=required_theorem_names,
            copyable_lean_stub=copyable_lean_stub,
        )
        if candidate_row is not None and conflict_present
        else None
    )

    source_ready = (
        candidate_row is not None
        and conflict_present
        and source_checks["module_path_exists"]
        and source_checks["namespace_found"]
        and not source_checks["missing_source_theorem_names"]
        and source_checks["theorem_guide_path_exists"]
        and not source_checks["missing_theorem_guide_mentions"]
        and not stub_lint_errors
    )
    scaffold_ready = candidate_row is not None and conflict_present and not stub_lint_errors
    if candidate_row is None:
        mapping_lint_status = "candidate_not_found"
    elif not conflict_present:
        mapping_lint_status = "not_fixture_candidate"
    elif source_ready:
        mapping_lint_status = "source_ready_existing_mapping"
    else:
        mapping_lint_status = "scaffold_ready_pending_lean_source"

    source_pinning_recipe = _source_pinning_recipe(
        namespace=namespace,
        module_path=module_path,
        theorem_guide_path=theorem_guide_path,
        required_theorem_names=required_theorem_names,
        copyable_lean_stub=copyable_lean_stub,
    )

    return {
        "schema": CERTIFICATE_FIXTURE_MAPPING_LINT_SCHEMA,
        "summary": {
            "candidate_found": candidate_row is not None,
            "candidate_base": int(candidate_base),
            "candidate_n": int(candidate_n),
            "candidate_m": int(candidate_m) if candidate_m is not None else None,
            "mapping_lint_status": mapping_lint_status,
            "source_ready": source_ready,
            "scaffold_ready": scaffold_ready,
            "promotes_claims": False,
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            "staging_note": (
                "fixture mapping lint stages a proposed Lean namespace/module "
                "mapping only; add source-pinned anchors intentionally after "
                "the Lean package and theorem-guide mentions exist"
            ),
        },
        "candidate": candidate,
        "proposed_mapping": {
            "namespace": namespace,
            "module_path": module_path,
            "theorem_guide_path": theorem_guide_path,
            "fixture_status_if_promoted": SOURCE_PINNED_FIXTURE_STATUS,
            "required_theorem_names": required_theorem_names,
            "qualified_theorem_names": source_checks["qualified_theorem_names"],
            "source_checks": source_checks,
            "copyable_lean_stub": copyable_lean_stub,
            "source_pinning_recipe": source_pinning_recipe,
            "lean_package_plan": lean_package_plan,
            "stub_lint_status": "passed" if not stub_lint_errors else "failed",
            "stub_lint_errors": stub_lint_errors,
        },
    }


def certificate_first_scaffold_mapping_lint_payload(
    *,
    namespace: str | None = None,
    namespace_prefix: str = DEFAULT_SCAFFOLD_NAMESPACE_PREFIX,
    module_path: str = "lean/QRTour/Examples.lean",
    theorem_guide_path: str = "lean/THEOREM_GUIDE.md",
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    max_lookahead_blocks: int = 128,
) -> dict[str, Any]:
    """Auto-select the first scaffold-ready, non-source-ready mapping candidate."""

    parsed_bases = _parse_bases(bases)
    rows = certificate_workbench_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    skipped_source_pinned = 0
    inspected_conflict_candidates = 0
    for row in rows:
        if row.get("group") != WORKBENCH_CASE_GROUP:
            continue
        if row.get("conflict_remainder_state") is None:
            continue
        inspected_conflict_candidates += 1
        if (int(row["base"]), int(row["n"])) in LEAN_FIXTURE_ANCHORS:
            skipped_source_pinned += 1
            continue

        candidate_namespace = namespace or _default_scaffold_namespace(
            row, namespace_prefix
        )
        payload = certificate_fixture_mapping_lint_payload(
            candidate_base=int(row["base"]),
            candidate_n=int(row["n"]),
            candidate_m=int(row["m"]),
            namespace=candidate_namespace,
            module_path=module_path,
            theorem_guide_path=theorem_guide_path,
            max_n=max_n,
            bases=parsed_bases,
            n_blocks=n_blocks,
            max_lookahead_blocks=max_lookahead_blocks,
        )
        if (
            payload["summary"]["scaffold_ready"]
            and not payload["summary"]["source_ready"]
        ):
            payload["summary"].update(
                {
                    "candidate_selection_mode": "first_scaffold_only",
                    "auto_selected_candidate": True,
                    "namespace_auto_generated": namespace is None,
                    "namespace_prefix": namespace_prefix,
                    "skipped_source_pinned_candidates": skipped_source_pinned,
                    "inspected_conflict_candidates": inspected_conflict_candidates,
                    "selection_note": (
                        "first ranked conflict certificate that is scaffold-ready "
                        "and not already source-ready after skipping source-pinned "
                        "fixture anchors"
                    ),
                }
            )
            return payload

    required_theorem_names = list(LEAN_FIXTURE_THEOREM_NAMES)
    fallback_namespace = namespace or f"{namespace_prefix}Candidate"
    return {
        "schema": CERTIFICATE_FIXTURE_MAPPING_LINT_SCHEMA,
        "summary": {
            "candidate_found": False,
            "candidate_base": None,
            "candidate_n": None,
            "candidate_m": None,
            "mapping_lint_status": "no_scaffold_ready_candidate",
            "source_ready": False,
            "scaffold_ready": False,
            "promotes_claims": False,
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            "candidate_selection_mode": "first_scaffold_only",
            "auto_selected_candidate": False,
            "namespace_auto_generated": namespace is None,
            "namespace_prefix": namespace_prefix,
            "skipped_source_pinned_candidates": skipped_source_pinned,
            "inspected_conflict_candidates": inspected_conflict_candidates,
            "staging_note": (
                "no scaffold-ready, non-source-ready conflict candidate was "
                "found under the requested bounds"
            ),
        },
        "candidate": None,
        "proposed_mapping": {
            "namespace": fallback_namespace,
            "module_path": module_path,
            "theorem_guide_path": theorem_guide_path,
            "fixture_status_if_promoted": SOURCE_PINNED_FIXTURE_STATUS,
            "required_theorem_names": required_theorem_names,
            "qualified_theorem_names": [
                f"{fallback_namespace}.{name}" for name in required_theorem_names
            ],
            "source_checks": None,
            "copyable_lean_stub": None,
            "source_pinning_recipe": _source_pinning_recipe(
                namespace=fallback_namespace,
                module_path=module_path,
                theorem_guide_path=theorem_guide_path,
                required_theorem_names=required_theorem_names,
                copyable_lean_stub=None,
            ),
            "lean_package_plan": None,
            "stub_lint_status": "not_run",
            "stub_lint_errors": [],
        },
    }


def certificate_lean_stub_rows(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, Any]]:
    """Return copyable Lean stub scaffold rows derived from fixture records."""

    fixtures = certificate_lean_fixture_rows(
        max_n=max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=top,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    rows: list[dict[str, Any]] = []
    for fixture in fixtures:
        stub = fixture["copyable_lean_stub"]
        lint_errors = _lint_copyable_lean_stub(fixture)
        rows.append(
            {
                "certificate_id": fixture["certificate_id"],
                "namespace": fixture["namespace"],
                "module_path": fixture["module_path"],
                "certificate_tuple": fixture["certificate_tuple"],
                "source_fixture_status": fixture["fixture_status"],
                "certificate_class": fixture["certificate_class"],
                "lean_readiness": fixture["lean_readiness"],
                "stub_scaffold_status": LEAN_STUB_SCAFFOLD_STATUS,
                "stub_kind": stub["kind"],
                "stub_theorem_name": stub["recommended_theorem_name"],
                "record_theorem_name": stub["record_theorem_name"],
                "projection_accessor": stub["projection_accessor"],
                "copyable_lean_code": stub["code"],
                "lint_status": "passed" if not lint_errors else "failed",
                "lint_errors": lint_errors,
                "open_boundary_ids": fixture["open_boundary_ids"],
            }
        )
    return rows


def certificate_lean_stub_payload(
    *,
    max_n: int = 1200,
    bases: Iterable[int] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> dict[str, Any]:
    """Return JSON-ready copyable Lean stubs with fixture-level lint results."""

    parsed_bases = _parse_bases(bases)
    stubs = certificate_lean_stub_rows(
        max_n=max_n,
        bases=parsed_bases,
        n_blocks=n_blocks,
        top=top,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    lint_failed = [stub for stub in stubs if stub["lint_status"] != "passed"]
    return {
        "schema": CERTIFICATE_LEAN_STUBS_SCHEMA,
        "summary": {
            "source_schema": CERTIFICATE_LEAN_FIXTURE_SCHEMA,
            "source_surface": "visibility-certificate-lean-fixtures",
            "max_n": max_n,
            "bases": list(parsed_bases),
            "requested_blocks": n_blocks,
            "emitted_stub_count": len(stubs),
            "lint_passed": len(stubs) - len(lint_failed),
            "lint_failed": len(lint_failed),
            "first_stub_theorem_name": (
                stubs[0]["stub_theorem_name"] if stubs else None
            ),
            "open_boundary_ids": list(OPEN_BOUNDARY_IDS),
            "scaffold_note": (
                "copy these stubs only after intentionally adding or mapping "
                "a finite Lean package; this is empirical tooling, not "
                "theorem promotion"
            ),
        },
        "stubs": stubs,
    }


__all__ = [
    "CertificateWorkbenchRecord",
    "CoefficientConflictCertificate",
    "LookaheadCertificate",
    "StateMapCertificate",
    "certificate_fixture_mapping_lint_payload",
    "certificate_lean_fixture_payload",
    "certificate_lean_fixture_rows",
    "certificate_lean_stub_payload",
    "certificate_lean_stub_rows",
    "certificate_workbench_rows",
    "observability_atlas_rows",
    "observability_instrument_comparison_rows",
    "observability_mod_stable_carry_loss_rows",
    "observability_next_source_shape_family_rows",
    "observability_program_atlas_rows",
    "observability_shape13_k4_mod_stable_carry_loss_rows",
    "observability_shape187_k188_family_rows",
    "observability_shape17_k4_family_rows",
    "observability_target_signature_rows",
    "observability_target_split_rows",
]
