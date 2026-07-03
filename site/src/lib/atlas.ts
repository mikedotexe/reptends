import claimRegistryData from '../../../data/claim_registry.json';
import counterexamplesData from '../../../data/counterexamples.json';
import exampleAtlasData from '../../../data/example_atlas.json';
import theoremWitnessesData from '../../../data/theorem_witnesses.json';
import vocabularyData from '../../../data/vocabulary.json';

export interface ClaimRecord {
  id: string;
  title: string;
  statement: string;
  status: 'classical' | 'reproved-here' | 'implemented-here' | 'empirical' | 'open';
  repo_status: string;
  proof_status: string;
  evidence: string[];
  vocabulary_ids: string[];
  source_ids: string[];
  counterexample_ids: string[];
}

export interface CounterexampleRecord {
  id: string;
  claim_id: string;
  legacy_claim: string;
  parameters: Record<string, number | string>;
  observed: string;
  replacement: string;
}

export interface VocabularyEntry {
  id: string;
  preferred_label: string;
  repo_aliases: string[];
  meaning: string;
  scope: string;
}

export interface TheoremWitnessRecord {
  id: string;
  claim_id: string;
  kind: 'theorem-witness' | 'empirical-witness' | 'open-target';
  label: string;
  tuple_display: string;
  parameters: Record<string, number | string | number[] | string[] | Record<string, number>>;
  summary: string;
  evidence: string[];
}

export interface ClaimWitnessRow {
  witness_id: string;
  claim_id: string;
  claim_title: string;
  claim_status: ClaimRecord['status'];
  kind: TheoremWitnessRecord['kind'];
  label: string;
  tuple_display: string;
  parameters: Record<string, number | string | number[] | string[] | Record<string, number>>;
  summary: string;
  evidence: string[];
}

export interface ClaimContext {
  related_claim_ids: string[];
  related_open_claim_ids: string[];
  matching_claim_ids: string[];
  matching_witness_ids: string[];
}

export interface SearchPreviewEntry {
  label: string;
  summary: string;
  command: string;
}

export interface ThroughlineSearchEntry extends SearchPreviewEntry {
  id: string;
  atlas_section_id: string | null;
}

export interface ThroughlineLadderEntry {
  id: string;
  label: string;
  claim_ids: string[];
  witness_ids: string[];
  counterexample_ids: string[];
  summary: string;
}

export interface ThroughlineRecord {
  id: string;
  kind: 'research-thesis';
  title: string;
  headline: string;
  status_note: string;
  claim_ids: string[];
  open_claim_ids: string[];
  witness_ids: string[];
  counterexample_ids: string[];
  featured_searches: ThroughlineSearchEntry[];
  ladder: ThroughlineLadderEntry[];
}

export interface OrbitCarryFrontierRow {
  group: 'orbit_layer_examples' | 'carry_layer_examples' | 'frontier_targets' | 'obstruction_families';
  label: string;
  n: number | null;
  members: number[] | null;
  row_kind: 'witness' | 'case-study' | 'open-target' | 'counterexample' | 'family-study';
  claim_context?: ClaimContext;
  witness_id?: string;
  counterexample_id?: string;
  summary?: string;
  signal?: string;
  observed?: string;
  replacement?: string;
  distinctive_feature?: string;
  implemented_boundary?: string;
  open_boundary?: string;
  summary_lines?: string[];
}

export interface StateMapFiberRecord {
  source_state: number;
  target_states: number[];
}

export interface StateMapPreimageFiberRecord {
  target_state: number;
  source_states: number[];
}

export interface StateCompressionTargetRecord {
  target_state: number;
  source_states: number[];
  preimage_size: number;
}

export interface ObservedStateMapProfile {
  source_kind: string;
  target_kind: string;
  source_state_count: number;
  image_state_count: number;
  is_functional: boolean;
  is_injective: boolean;
  max_fiber_size: number;
  max_preimage_size: number;
  fiber_signature: string;
  preimage_signature: string;
  ambiguity_signature: string;
  fibers: StateMapFiberRecord[];
  preimage_fibers: StateMapPreimageFiberRecord[];
  compression_targets: StateCompressionTargetRecord[];
  ambiguous_sources: StateMapFiberRecord[];
}

export interface StateAlignmentRow {
  position: number;
  coefficient: number;
  carry_state: number;
  remainder_state: number;
  block_value: number;
}

export interface StateMergingSameCoreRow {
  base: number;
  core_n: number;
  members: number[];
  selected_members: number[];
  selected_regimes: string[];
  selected_obstruction_classes: string[];
  forward_preimage_signatures: string[];
  reverse_ambiguity_signatures: string[];
  relabeling_members: number[];
  hidden_members: number[];
  visible_members: number[];
  compressed_class_path: string[];
  compressed_obstruction_path: string[];
  first_relabeling_member: number | null;
  first_non_relabeling_member: number | null;
  first_hidden_member: number | null;
  first_visible_member: number | null;
  has_visible_after_hidden: boolean;
  has_rehidden_after_visible: boolean;
  visibility_behavior: string;
  onset_kind: string;
  has_nonmonotone_hidden_visible_switching: boolean;
  hidden_visible_switch_count: number;
  phase_summary: string;
  has_regime_disagreement: boolean;
  has_obstruction_class_disagreement: boolean;
  has_forward_preimage_disagreement: boolean;
  has_reverse_ambiguity_disagreement: boolean;
  has_hidden_graph_obstruction_member: boolean;
  has_visible_preimage_compression_member: boolean;
  crosses_relabeling_hidden_visible_classes: boolean;
  has_state_merging_disagreement: boolean;
  related_claim_ids: string[];
  related_open_claim_ids: string[];
  matching_claim_ids: string[];
  matching_witness_ids: string[];
}

export interface StateMergingCaseStudyRecord {
  label: string;
  n: number;
  base: number;
  explanation: string;
  theorem_candidate: string;
  heuristic_note: string;
  counterexample_target: string;
  primary_vocabulary_id: string;
  summary_lines: string[];
  selected_coordinate: {
    m: number;
    B: number;
    q: number;
    k: number;
  };
  factorization_regime: string;
  obstruction_class: string;
  obstruction_summary: string;
  observed_alignment_bijection: boolean;
  carry_state_count: number;
  remainder_state_count: number;
  carry_class_count: number;
  remainder_class_count: number;
  graph_state_gap: number;
  minimized_class_gap: number;
  profile_class: string;
  transition_signature: string[];
  forward_profile: ObservedStateMapProfile;
  reverse_profile: ObservedStateMapProfile;
  compression_targets: StateCompressionTargetRecord[];
  forward_preimage_signature: string;
  reverse_preimage_signature: string;
  forward_ambiguity_signature: string;
  reverse_ambiguity_signature: string;
  alignment_rows: StateAlignmentRow[];
  claim_context: ClaimContext;
}

export interface StateMergingFamilyStudyRecord {
  label: string;
  members: number[];
  explanation: string;
  theorem_candidate: string;
  heuristic_note: string;
  counterexample_target: string;
  primary_vocabulary_id: string;
  summary_lines: string[];
  family_row: StateMergingSameCoreRow;
  member_cases: StateMergingCaseStudyRecord[];
}

export interface CanonicalExampleRecord {
  category: string;
  explanation: string;
  label: string;
  n: number;
  primary_vocabulary_id: string;
}

export interface BridgeLeaderboardEntry {
  B: number;
  base: number;
  explanation: string;
  is_trivial_period: boolean;
  k: number;
  m: number;
  n: number;
  period: number;
  periodic_modulus: number;
  preperiod_digits: number;
  primary_vocabulary_id: string;
  q: number;
  q_is_one: boolean;
  score: number;
  visible_prefix: number;
}

export interface CompositeLeaderboardEntry {
  base: number;
  best_k: number | null;
  best_m: number | null;
  best_q: number | null;
  component_count: number;
  explanation: string;
  global_order: number;
  n: number;
  preperiod_digits: number;
  primary_vocabulary_id: string;
  score: number;
  stripped_modulus: number;
}

export interface PrimeQRLeaderboardEntry {
  base: number;
  explanation: string;
  p: number;
  preferred_k: number;
  preferred_stride: number;
  primary_vocabulary_id: string;
  reptend_type: string;
  score: number;
  stride_count: number;
}

export interface ExampleAtlas {
  claim_witnesses: {
    featured_ids: string[];
    rows: ClaimWitnessRow[];
  };
  case_studies: {
    orbit_carry_frontier: {
      orbit_layer_examples: OrbitCarryFrontierRow[];
      carry_layer_examples: OrbitCarryFrontierRow[];
      frontier_targets: OrbitCarryFrontierRow[];
      obstruction_families: OrbitCarryFrontierRow[];
    };
    carry_dfa: Array<{
      claim_context: ClaimContext;
      distinctive_feature: string;
      factorization_status: {
        implemented: string;
        open_boundary: string;
      };
      label: string;
      n: number;
      summary_lines: string[];
    }>;
    carry_selector: Array<{
      base: number;
      counterexample_target: string;
      explanation: string;
      heuristic_note: string;
      label: string;
      n: number;
      primary_vocabulary_id: string;
      profile: {
        finite_word_only_modes: number[];
        has_isolated_relabeling_window: boolean;
        profile_class: string;
        quotient_modes: number[];
        relabeling_modes: number[];
        selected_k: number | null;
        selected_m: number | null;
        selected_q: number | null;
        transition_signature: string[];
      };
      summary_lines: string[];
      theorem_candidate: string;
    }>;
    carry_selector_families: Array<{
      counterexample_target: string;
      explanation: string;
      heuristic_note: string;
      label: string;
      members: number[];
      primary_vocabulary_id: string;
      summary_lines: string[];
      theorem_candidate: string;
    }>;
    state_merging: StateMergingCaseStudyRecord[];
    state_merging_families: StateMergingFamilyStudyRecord[];
    visibility: Array<{
      claim_context: ClaimContext;
      counterexample_target: string;
      explanation: string;
      family_id: string;
      heuristic_note: string;
      label: string;
      n: number;
      profile: {
        B: number;
        agreement_identity_holds: boolean;
        base: number;
        certified_lookahead_blocks: number;
        exact_gap_numerator: number;
        first_incoming_carry_position: number | null;
        first_local_overflow_position: number | null;
        first_mismatch_position: number | null;
        incoming_carry_formula_holds: boolean;
        k: number;
        lookahead_lower_bound: number;
        lookahead_certificate_matches: boolean;
        lookahead_blocks: number;
        m: number;
        mismatch_regime: string;
        period: number;
        periodic_modulus: number;
        preperiod_digits: number;
        q: number;
        raw_prefix_agreement_length: number;
        requested_blocks: number;
      };
      summary_lines: string[];
      theorem_candidate: string;
    }>;
    visibility_families: Array<{
      counterexample_target: string;
      explanation: string;
      heuristic_note: string;
      label: string;
      members: number[];
      primary_vocabulary_id: string;
      summary_lines: string[];
      theorem_candidate: string;
    }>;
    composite_examples: Array<{
      actual_k: number | null;
      actual_m: number | null;
      actual_q: number | null;
      carry_graph_class_count: number;
      carry_state_count: number;
      carry_summary: string;
      coordinate_summary: string;
      core_k: number | null;
      core_m: number | null;
      core_q: number | null;
      crt_summary: string;
      explanation: string;
      family_id: string;
      label: string;
      n: number;
      preperiod_summary: string;
    }>;
    composite_families: Array<{
      carry_focus: string;
      coordinate_focus: string;
      crt_focus: string;
      explanation: string;
      label: string;
      members: number[];
      preperiod_focus: string;
      primary_vocabulary_id: string;
    }>;
  };
  canonical_examples: CanonicalExampleRecord[];
  dataset_kind: string;
  throughlines: {
    featured_ids: string[];
    rows: ThroughlineRecord[];
  };
  leaderboards: {
    bridge_nontrivial: BridgeLeaderboardEntry[];
    bridge_q1: BridgeLeaderboardEntry[];
    composite_crt: CompositeLeaderboardEntry[];
    prime_qr: PrimeQRLeaderboardEntry[];
  };
  manifest: {
    build_command: string;
    builder: string;
    normalization: string;
    publication_layer: string;
    source_files: string[];
  };
  metadata: {
    base: number;
    max_n: number;
    max_p: number;
    publication_layer: string;
    standard_label_first: boolean;
    top: number;
  };
  provenance: {
    base: number;
    cross_base_selector_bases?: number[];
    max_n: number;
    max_p: number;
    standard_label_first: boolean;
    top: number;
  };
  research_layers: {
    carry_selector: {
      bases: Array<{
        base: number;
        classification_bound: number;
        finite_word_only: number;
        isolated_k_one_relabeling: number;
        isolated_non_k_one_relabeling: number;
        max_m: number;
        mixed_without_relabeling: number;
        n_blocks: number;
        non_k_one_count: number;
        profile_count: number;
        publication_decision: string;
        quotient_only: number;
        repeated_k_one_relabeling: number;
        repeated_non_k_one_relabeling: number;
        same_core_disagreement_count: number;
        same_core_multi_member_count: number;
        sample_non_k_one_examples: string[];
        sample_same_core_families: string[];
        summary_lines: string[];
      }>;
      classification_bound: number;
      decision: string;
      publication_status: string;
    };
    state_merging: {
      base: number;
      classification_bound: number;
      decision: string;
      hidden_graph_obstruction_count: number;
      publication_status: string;
      quotient_candidate_only_count: number;
      representative_hidden_ns: number[];
      representative_visible_ns: number[];
      summary_lines: string[];
      visible_preimage_compression_count: number;
      rows: StateMergingCaseStudyRecord[];
    };
    state_merging_same_core: {
      base: number;
      decision: string;
      publication_status: string;
      rows: StateMergingSameCoreRow[];
    };
  };
  schema_version: string;
}

export const claimRegistry = claimRegistryData as unknown as ClaimRecord[];
export const counterexamples = counterexamplesData as unknown as CounterexampleRecord[];
export const theoremWitnessRegistry = theoremWitnessesData as unknown as TheoremWitnessRecord[];
export const vocabulary = vocabularyData as unknown as VocabularyEntry[];
export const exampleAtlas = exampleAtlasData as unknown as ExampleAtlas;

export const featuredClaims = claimRegistry.filter(claim =>
  [
    'series_q_weighted_identity',
    'qr_stride_classification',
    'crt_period_lcm',
    'carry_window_transducer',
    'small_k_visibility_heuristic',
  ].includes(claim.id)
);

export const openClaims = claimRegistry.filter(claim => claim.status === 'open');
export const claimById = new Map(claimRegistry.map(claim => [claim.id, claim]));
export const theoremWitnessById = new Map(theoremWitnessRegistry.map(witness => [witness.id, witness]));
export const vocabularyById = new Map(vocabulary.map(entry => [entry.id, entry]));

export const featuredCounterexamples = counterexamples.filter(counterexample =>
  [
    'legacy_unweighted_series_37',
    'legacy_full_even_19',
    'legacy_half_consecutive_31',
  ].includes(counterexample.id)
);

export const canonicalExamples = exampleAtlas.canonical_examples;
export const researchTheses = exampleAtlas.throughlines.rows;
export const featuredThroughline = exampleAtlas.throughlines.featured_ids
  .map(id => researchTheses.find(record => record.id === id))
  .find((record): record is ThroughlineRecord => record !== undefined) ?? null;
export const claimWitnessRows = exampleAtlas.claim_witnesses.rows;
export const featuredClaimWitnesses = exampleAtlas.claim_witnesses.featured_ids
  .map(id => claimWitnessRows.find(row => row.witness_id === id))
  .filter((row): row is ClaimWitnessRow => row !== undefined);
export const theoremWitnesses = claimWitnessRows.filter(row => row.kind === 'theorem-witness');
export const empiricalWitnesses = claimWitnessRows.filter(row => row.kind === 'empirical-witness');
export const openClaimTargets = claimWitnessRows.filter(row => row.kind === 'open-target');
export const bridgeHighlights = exampleAtlas.leaderboards.bridge_nontrivial;
export const bridgeQ1Highlights = exampleAtlas.leaderboards.bridge_q1;
export const compositeHighlights = exampleAtlas.leaderboards.composite_crt;
export const primeQRHighlights = exampleAtlas.leaderboards.prime_qr;
export const orbitCarryFrontier = exampleAtlas.case_studies.orbit_carry_frontier;
export const stateMergingCaseStudies = exampleAtlas.case_studies.state_merging;
export const stateMergingFamilyStudies = exampleAtlas.case_studies.state_merging_families;
export const stateMergingResearchLayer = exampleAtlas.research_layers.state_merging;
export const stateMergingSameCoreResearchLayer = exampleAtlas.research_layers.state_merging_same_core;
export const visibilityCaseStudies = exampleAtlas.case_studies.visibility;
export const visibilityFamilyStudies = exampleAtlas.case_studies.visibility_families;

const throughlineSearchPreview = (featuredThroughline?.featured_searches ?? []).map(entry => ({
  label: entry.label,
  summary: entry.summary,
  command: entry.command,
}));

const searchPreviewRaw: SearchPreviewEntry[] = [
  ...throughlineSearchPreview,
  {
    label: 'Readable q-weighted bridges',
    summary: 'Highlights moduli like 37 and 97 where small k makes the early coefficients easy to see.',
    command: 'search-reptends small-residue-coordinates --max 500 --top 20',
  },
  {
    label: 'Pure q=1 bridges',
    summary: 'Separates nontrivial bridge cases like 97 and 996 from trivial period-1 shortcuts.',
    command: 'search-reptends small-residue-coordinates-q1 --max 1500 --top 10',
  },
  {
    label: 'Prime QR examples',
    summary: 'Ranks primes where a small stride produces a generator of the QR subgroup.',
    command: 'search-reptends prime-qr-generators --max 500 --top 10',
  },
  {
    label: 'Legacy counterexamples',
    summary: 'Surfaces exact failures of the old “all even” and “all consecutive” stride heuristics.',
    command: 'search-reptends legacy-counterexamples --max 500 --bases 2,7,10,12',
  },
  {
    label: 'Composite CRT profiles',
    summary: 'Exports stripped moduli, preperiod lengths, and prime-power order data for composites like 996.',
    command: 'search-reptends composite-profiles --max 500',
  },
  {
    label: 'Carried-prefix visibility',
    summary: 'Exports exact raw-prefix agreement lengths, incoming-carry positions, and stabilization lookahead for Track 16 examples.',
    command: 'search-reptends visibility-profiles --max 500 --blocks 8',
  },
  {
    label: 'Visibility counterexamples',
    summary: 'Finds cases like 97 and 249 where incoming carry arrives before the local overflow boundary.',
    command: 'search-reptends visibility-counterexamples --max 500 --blocks 8',
  },
  {
    label: 'Same-core visibility families',
    summary: 'Compares denominators to their stripped periodic cores and surfaces exact-law and interval-law shift families across bases.',
    command: 'search-reptends same-core-visibility --base 12 --max 200 --blocks 8',
  },
  {
    label: 'Carry/DFA factorization',
    summary: 'Exports Track 17 regimes separating trivial state relabeling, quotient candidates, and bounded counterexamples to stronger claims.',
    command: 'search-reptends carry-factorization --max 500 --blocks 8',
  },
  {
    label: 'Carry selector profiles',
    summary: 'Shows how the Track 17 regime changes across candidate block widths, including isolated relabeling windows and same-core divergences.',
    command: 'search-reptends carry-factorization-selector --max 300 --blocks 8',
  },
  {
    label: 'Carry selector non-k1',
    summary: 'Isolates the selected non-k = 1 state-relabeling windows that are currently the strongest Track 17 arithmetic signal.',
    command: 'search-reptends carry-selector-non-k1 --max 400 --blocks 8',
  },
  {
    label: 'Carry selector same-core',
    summary: 'Groups selector profiles by stripped periodic core to surface relabeling-window loss, shift, and disagreement families.',
    command: 'search-reptends carry-selector-same-core --max 400 --blocks 8',
  },
  {
    label: 'Carry selector research',
    summary: 'Summarizes cross-base selector evidence showing non-k = 1 relabeling windows and same-core disagreement as stable Track 17 signal.',
    command: 'search-reptends carry-selector-research --max 120 --bases 7,10,12 --blocks 8',
  },
  {
    label: 'Published example atlas',
    summary: 'Builds the schema-versioned published atlas used by docs, the note, and site surfaces.',
    command: 'search-reptends published-atlas --max 1200 --top 8 --output data/example_atlas.json',
  },
];

export const searchPreview = searchPreviewRaw.filter((entry, index, entries) =>
  entries.findIndex(candidate => candidate.command === entry.command) === index
);

export function displayTerm(vocabularyId: string, standardMode: boolean): {
  primary: string;
  secondary: string;
} {
  const entry = vocabularyById.get(vocabularyId);
  if (!entry) {
    return { primary: vocabularyId, secondary: '' };
  }

  if (standardMode) {
    return {
      primary: entry.preferred_label,
      secondary: entry.repo_aliases.join(', '),
    };
  }

  return {
    primary: entry.repo_aliases[0] ?? entry.preferred_label,
    secondary: entry.preferred_label,
  };
}
