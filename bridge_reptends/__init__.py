"""
Bridge reptend analysis - geometric series structure in repeating decimals.

## The Core Algebraic Identity

For a block base B = base^m and modulus N, write:

    B = qN + k, with 0 <= k < N

Then:

    1/N = q/(B-k) = (q/B) × 1/(1 - k/B) = Σ q*k^j / B^(j+1)

The literal power pattern 1, k, k², k³, ... is the special case q = 1,
equivalently N = B - k.

When k is small ("bridge" denominators like N = 10² - 3 = 97), the power
pattern is visible for many blocks before carry disrupts it.

## The Three Layers

| Layer    | What                                    | Universal? |
|----------|-----------------------------------------|------------|
| Skeleton | Raw coefficients q*k^j (k^j when q=1)  | Yes, any N |
| Carry    | Overflow correction when k^j ≥ B^m      | Yes, any N |
| Closure  | Cyclic wrap after ord_N(B) blocks       | Yes, any N |

## The Prime Bonus

When N is prime, the multiplicative group (ℤ/pℤ)* splits into exactly
two cosets (QR and NQR). This explains:
- Why certain k values generate half the group
- The trichotomy (full/half/degenerate reptends)
- Base-invariant stride counts

But the skeleton structure works for 1/96, 1/996, 1/9996 just as well.

Core functions:
    # Universal
    multiplicative_order - Compute ord_n(a)
    long_division_remainders - Get remainder sequence from 1/n
    stride_order - Compute ord_p(base^m) via order/gcd
    reptend_type - Classify ord_p(base) as full / half / degenerate
    orbit_weave_analysis - Algebraic decomposition R = W + F
    compare_raw_coefficients_to_blocks - Compare q*k^j coefficients to actual blocks
    render_raw_coefficient_analysis - Visualize the raw coefficient layer plus carry

    # Prime-specific (requires prime p)
    is_qr - Test quadratic residue membership (Euler's criterion)
    is_qr_generator - Check if k generates QR subgroup
    find_qr_strides - Find all m where base^m is QR-generator
    analyze_prime - Complete analysis of a prime's reptend structure
    analyze_coset_structure - Analyze coset/block structure

Example:
    >>> from bridge_reptends import print_skeleton_analysis
    >>> print_skeleton_analysis(996)  # Works for composite!
    # Shows: skeleton powers, carried values, actual long-division blocks

    >>> from bridge_reptends import analyze_prime, is_qr
    >>> analysis = analyze_prime(97, base=10)  # Prime-specific
    >>> print(f"3 is {'QR' if is_qr(3, 97) else 'NQR'} mod 97")
    3 is QR mod 97

Authors: Mike & Claude
Date: December 2025
"""

from .analysis import (
    multiplicative_order,
    long_division_remainders,
    stride_order,
    reptend_type,
    find_generator,
    is_qr_generator,
    find_qr_strides,
    analyze_prime,
    stride_fingerprint,
    PrimeAnalysis,
)

from .coset import (
    is_qr,
    coset_of,
    format_digit,
    find_block_structure,
    get_blocks,
    get_block_remainders,
    analyze_coset_structure,
    compare_coset_representatives,
    BlockStructure,
    Block,
    CosetAnalysis,
    DIGIT_CHARS,
)

from .orbit_weave import (
    orbit_weave_analysis,
    reptend_integer,
    weave,
    flux,
    verify_decomposition,
    best_bridge_mode,
    strip_base_factors,
    factorize,
    phi,
    carmichael_lambda,
    OrbitWeaveAnalysis,
    # Skeleton + carry analysis
    skeleton_vs_actual,
    print_skeleton_analysis,
    raw_series_blocks,
    raw_power_blocks,
    apply_carry,
    # Orbit Core: good coordinates
    find_good_modes,
    canonical_fraction,
)

from .composite import (
    PrimePowerPeriod,
    PrimePowerLiftingStep,
    PrimePowerLiftingFamily,
    CRTStep,
    CRTPeriodProfile,
    CompositeCaseStudy,
    CompositeFamilyCaseStudy,
    preperiod_length,
    prime_power_components,
    reconstruct_from_crt,
    crt_period_profile,
    crt_remainder_orbit,
    canonical_composite_case_studies,
    prime_power_lifting_family,
    canonical_composite_family_case_studies,
)

from .transducer import (
    CarryTransition,
    CarryRun,
    CarryGraphEdge,
    StateGraphEdge,
    StateGraph,
    MinimizedStateGraph,
    CarryStateSummary,
    RemainderTransition,
    RemainderRun,
    StateAlignment,
    ObservedStateMap,
    FactorizationDecisionReport,
    FactorizationSelectorStep,
    CarryFactorizationSelectorProfile,
    SelectorProfileComparison,
    CarrySelectorCaseStudy,
    CarrySelectorFamilyStudy,
    CarryRemainderComparison,
    CarryDFACase,
    CarryTransducer,
    CarryWindowExample,
    remainder_dfa_run,
    carry_window_example,
    carry_remainder_comparison,
    canonical_carry_dfa_examples,
    canonical_carry_selector_case_studies,
    canonical_carry_selector_family_studies,
    select_carry_factorization_prefer_m,
    carry_factorization_selector_profile,
    compare_carry_selector_profiles,
    carry_selector_profile_class,
    carry_selector_profile_rows,
    carry_selector_research_rows,
    non_k_one_state_relabeling_rows,
    same_core_selector_family_rows,
    carry_factorization_rows,
)

from .visibility import (
    VisibilityProfile,
    VisibilityCaseStudy,
    VisibilityFamilyStudy,
    SameCoreVisibilityComparison,
    incoming_carry_value,
    predicted_first_incoming_carry_position,
    predicted_raw_prefix_agreement_length,
    lookahead_tail_mass_lower_bound,
    lookahead_gap_numerator,
    lookahead_certificate_holds,
    certified_lookahead_blocks,
    carried_prefix_visibility_profile,
    canonical_visibility_case_studies,
    canonical_visibility_family_studies,
    select_same_core_prefer_m,
    same_core_visibility_comparison,
    visibility_profile_rows,
    incoming_carry_counterexample_rows,
    same_core_visibility_rows,
)

from .registry import (
    LiteratureSource,
    VocabularyEntry,
    CounterexampleRecord,
    ClaimRecord,
    LeanModuleRecord,
    TheoremWitnessRecord,
    load_literature_map,
    load_vocabulary,
    load_counterexamples,
    load_claim_registry,
    load_lean_module_index,
    load_theorem_witnesses,
    literature_lookup,
    vocabulary_lookup,
    counterexample_lookup,
    claim_lookup,
    lean_module_lookup,
    theorem_witness_lookup,
    theorem_witnesses_by_claim,
    claims_by_status,
    status_counts,
    open_claims,
    render_registry_summary_lines,
    render_open_claim_lines,
    render_claim_table_lines,
    render_vocabulary_table_lines,
    render_lean_module_index_lines,
    render_theorem_witness_summary_lines,
    render_theorem_witness_table_lines,
)

from .search import (
    BridgeCandidate,
    PrimeQRExample,
    CompositeHighlight,
    CanonicalExample,
    LegacyCounterexample,
    rank_bridge_candidates,
    rank_q_one_bridges,
    rank_prime_qr_examples,
    rank_composite_highlights,
    build_claim_witness_rows,
    build_example_atlas,
    find_legacy_counterexamples,
    composite_profile_rows,
)

# Standard-label-first aliases. Legacy names remain exported for compatibility.
body_term = weave
correction_term = flux
find_small_residue_block_coordinates = find_good_modes
compare_raw_coefficients_to_blocks = skeleton_vs_actual
render_raw_coefficient_analysis = print_skeleton_analysis
prime_power_order_lifting_family = prime_power_lifting_family
canonical_composite_families = canonical_composite_family_case_studies
build_published_example_atlas = build_example_atlas
build_visibility_profiles = visibility_profile_rows

__all__ = [
    # analysis.py
    "multiplicative_order",
    "long_division_remainders",
    "stride_order",
    "reptend_type",
    "find_generator",
    "is_qr_generator",
    "find_qr_strides",
    "analyze_prime",
    "stride_fingerprint",
    "PrimeAnalysis",
    # coset.py
    "is_qr",
    "coset_of",
    "format_digit",
    "find_block_structure",
    "get_blocks",
    "get_block_remainders",
    "analyze_coset_structure",
    "compare_coset_representatives",
    "BlockStructure",
    "Block",
    "CosetAnalysis",
    "DIGIT_CHARS",
    # orbit_weave.py
    "orbit_weave_analysis",
    "reptend_integer",
    "body_term",
    "correction_term",
    "weave",
    "flux",
    "verify_decomposition",
    "best_bridge_mode",
    "strip_base_factors",
    "factorize",
    "phi",
    "carmichael_lambda",
    "OrbitWeaveAnalysis",
    "compare_raw_coefficients_to_blocks",
    "render_raw_coefficient_analysis",
    "skeleton_vs_actual",
    "print_skeleton_analysis",
    "raw_series_blocks",
    "raw_power_blocks",
    "apply_carry",
    # Orbit Core: good coordinates
    "find_small_residue_block_coordinates",
    "find_good_modes",
    "canonical_fraction",
    # composite.py
    "PrimePowerPeriod",
    "PrimePowerLiftingStep",
    "PrimePowerLiftingFamily",
    "CRTStep",
    "CRTPeriodProfile",
    "CompositeCaseStudy",
    "CompositeFamilyCaseStudy",
    "preperiod_length",
    "prime_power_components",
    "reconstruct_from_crt",
    "crt_period_profile",
    "crt_remainder_orbit",
    "canonical_composite_case_studies",
    "prime_power_lifting_family",
    "prime_power_order_lifting_family",
    "canonical_composite_family_case_studies",
    "canonical_composite_families",
    # transducer.py
    "CarryTransition",
    "CarryRun",
    "CarryGraphEdge",
    "StateGraphEdge",
    "StateGraph",
    "MinimizedStateGraph",
    "CarryStateSummary",
    "RemainderTransition",
    "RemainderRun",
    "StateAlignment",
    "ObservedStateMap",
    "FactorizationDecisionReport",
    "FactorizationSelectorStep",
    "CarryFactorizationSelectorProfile",
    "SelectorProfileComparison",
    "CarrySelectorCaseStudy",
    "CarrySelectorFamilyStudy",
    "CarryRemainderComparison",
    "CarryDFACase",
    "CarryTransducer",
    "CarryWindowExample",
    "remainder_dfa_run",
    "carry_window_example",
    "carry_remainder_comparison",
    "canonical_carry_dfa_examples",
    "canonical_carry_selector_case_studies",
    "canonical_carry_selector_family_studies",
    "select_carry_factorization_prefer_m",
    "carry_factorization_selector_profile",
    "compare_carry_selector_profiles",
    "carry_selector_profile_class",
    "carry_selector_profile_rows",
    "carry_selector_research_rows",
    "non_k_one_state_relabeling_rows",
    "same_core_selector_family_rows",
    "carry_factorization_rows",
    # visibility.py
    "VisibilityProfile",
    "VisibilityCaseStudy",
    "VisibilityFamilyStudy",
    "SameCoreVisibilityComparison",
    "incoming_carry_value",
    "predicted_first_incoming_carry_position",
    "predicted_raw_prefix_agreement_length",
    "lookahead_tail_mass_lower_bound",
    "lookahead_gap_numerator",
    "lookahead_certificate_holds",
    "certified_lookahead_blocks",
    "carried_prefix_visibility_profile",
    "canonical_visibility_case_studies",
    "canonical_visibility_family_studies",
    "select_same_core_prefer_m",
    "same_core_visibility_comparison",
    "visibility_profile_rows",
    "incoming_carry_counterexample_rows",
    "same_core_visibility_rows",
    # registry.py
    "LiteratureSource",
    "VocabularyEntry",
    "CounterexampleRecord",
    "ClaimRecord",
    "LeanModuleRecord",
    "TheoremWitnessRecord",
    "load_literature_map",
    "load_vocabulary",
    "load_counterexamples",
    "load_claim_registry",
    "load_lean_module_index",
    "load_theorem_witnesses",
    "literature_lookup",
    "vocabulary_lookup",
    "counterexample_lookup",
    "claim_lookup",
    "lean_module_lookup",
    "theorem_witness_lookup",
    "theorem_witnesses_by_claim",
    "claims_by_status",
    "status_counts",
    "open_claims",
    "render_registry_summary_lines",
    "render_open_claim_lines",
    "render_claim_table_lines",
    "render_vocabulary_table_lines",
    "render_lean_module_index_lines",
    "render_theorem_witness_summary_lines",
    "render_theorem_witness_table_lines",
    # search.py
    "BridgeCandidate",
    "PrimeQRExample",
    "CompositeHighlight",
    "CanonicalExample",
    "LegacyCounterexample",
    "rank_bridge_candidates",
    "rank_q_one_bridges",
    "rank_prime_qr_examples",
    "rank_composite_highlights",
    "build_claim_witness_rows",
    "build_published_example_atlas",
    "build_example_atlas",
    "find_legacy_counterexamples",
    "composite_profile_rows",
    "build_visibility_profiles",
]

__version__ = "0.2.0"
