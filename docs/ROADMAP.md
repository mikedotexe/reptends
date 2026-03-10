# Hardening Roadmap

This is the working todo list for the next repository passes. It converts the current priorities into concrete tracks with deliverables, sequencing, and acceptance criteria.

## Operating Rules

- Use the standard term first and the repo alias second.
- Tag every public mathematical claim as `classical`, `reproved-here`, `implemented-here`, `empirical`, or `open`.
- Keep prime-only structure separate from general composite/base-expansion structure.
- Preserve explicit counterexamples to older prose so they do not reappear.
- Treat the machine-readable registry files in [data/claim_registry.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/claim_registry.json), [data/counterexamples.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/counterexamples.json), and [data/vocabulary.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/vocabulary.json) as the intended source of truth.

## Execution Order

1. Collaborator docs and empirical-note framing
2. Registry-driven outward surfaces and drift checks
3. Search ranking and dataset quality
4. Composite and carry-transducer exposition
5. Lean proof expansion
6. Full site rewrite around the registry
7. Registry-driven publishing and sync tooling
8. Lean completion of the remaining exact core claims
9. Carry/DFA theory as a first-class mathematical layer
10. Composite theory beyond the stripped-core baseline
11. Dataset publication and larger reproducible sweeps
12. Vocabulary/API normalization across code and CLI
13. Expository note / monograph pass
14. Agda proof-surface audit and correspondence
15. Agda pedagogical core hardening
16. Exact carried-prefix visibility threshold framework
17. Canonical carry/DFA factorization research framework
18. Formal-systems integration and release snapshot

## Track 1: Collaborator Docs and Empirical Notes

Status: `implemented`

Why this matters:

- `AGENTS.md` and `CLAUDE.md` still contain the old unweighted series claim and the false `3 is NQR mod 97` statement.
- `DISCOVERIES.md` is mathematically improved, but its framing still suggests theorem-level novelty when much of the content is classical or empirical.

Todo:

- [x] Update [AGENTS.md](/Users/mikepurvis/other/quadratic-residue-reptends/AGENTS.md) to the exact `B = qN + k` identity, the exact QR-stride classification, and the standardized vocabulary.
- [x] Update [CLAUDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/CLAUDE.md) in the same way.
- [x] Reframe or rename [DISCOVERIES.md](/Users/mikepurvis/other/quadratic-residue-reptends/DISCOVERIES.md) so it reads as empirical notes and exact consequences, not novelty claims.
- [x] Add a short collaborator-facing rule that public prose must cite the proof-status atlas before introducing a theorem-level statement.

Acceptance criteria:

- No collaborator/agent doc repeats the old `Σ k^j / B^(j+1)` claim without `q`.
- No collaborator/agent doc repeats the legacy “all even strides” or “all consecutive strides” tables.
- The repo has no high-visibility file that conflates `classical` and `empirical` results.

## Track 2: Registry-Driven Surfaces and Drift Checks

Status: `implemented`

Why this matters:

- The new registry exists, but it is not yet authoritative.
- README, site prose, and collaborator docs can still drift independently.

Todo:

- [x] Add a drift-check script or test that scans public docs for banned legacy phrases and stale formulas.
- [x] Add a generated or semi-generated summary path from the registry into the README and major docs.
- [x] Normalize claim IDs, source IDs, and vocabulary IDs so they can be reused consistently in docs, UI, and search outputs.
- [x] Add a small “open claims” registry section so unresolved conjectural language is separated from proved or classical material.

Acceptance criteria:

- A test fails if public docs reintroduce the false universal series or legacy stride heuristics.
- README and site-facing summaries can be traced back to the claim registry rather than handwritten restatements.
- New theorem statements have a claim ID before they appear in public docs.

## Track 3: Search Ranking and Dataset Quality

Status: `implemented`

Why this matters:

- The current bridge ranking is mathematically correct but low-signal because trivial period-1 examples dominate.
- The search layer should surface instructive examples, not merely small residues.

Todo:

- [x] Redesign ranking in [bridge_reptends/search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py) to separate trivial period-1 examples from instructive nontrivial ones.
- [x] Add distinct leaderboards for:
  - `q = 1` bridge cases
  - nontrivial period bridge cases
  - composite/CRT examples
  - prime QR examples
- [x] Add canonical dataset outputs under `data/` for a small, curated example atlas.
- [x] Add ranking criteria that reward visible prefix length, nontrivial period, and canonical structure over trivial decimal shortcuts.

Acceptance criteria:

- Search outputs highlight `37`, `97`, `249`, `996`, and at least one prime QR example without being buried by trivial period-1 cases.
- Dataset files are stable enough to be referenced from docs and the site.
- Search results explain why an example is interesting in standardized vocabulary.

## Track 4: Composite and Carry-Transducer Exposition

Status: `implemented`

Why this matters:

- The repo now has useful composite and transducer code, but those ideas are not yet first-class in the exposition.
- This is one of the best places to create genuine repository value without overclaiming theorem novelty.

Todo:

- [x] Deepen [bridge_reptends/composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py) examples around `21`, `27`, `249`, and `996`.
- [x] Add an explicit relationship between CRT local orders, Carmichael bounds, and the global period.
- [x] Extend [bridge_reptends/transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py) with reachable-state summaries and state-graph export helpers.
- [x] Add docs or examples showing how the carry transducer relates to the long-division DFA and the raw coefficient layer.
- [x] Add at least one small example where the transducer perspective explains a carry pattern more clearly than raw block tables.

Acceptance criteria:

- Composite examples are documented as first-class cases, not as prime leftovers.
- The carry layer is described in standard automata/transducer language.
- The repo can expose a concrete carry-state summary for a named example.

## Track 5: Lean Proof Expansion

Status: `implemented`

Why this matters:

- The proof atlas is already stronger than before, but the next signal gain comes from formalizing the remaining central exact statements.

Todo:

- [x] Formalize the `φ((p-1)/2)` QR-stride count theorem in Lean.
- [x] Formalize the CRT period `lcm` theorem for coprime prime-power components.
- [x] Formalize the prime-by-prime valuation ceiling theorem behind the stripped-base-factor preperiod formula.
- [x] Update the proof-status atlas as each theorem moves from computational evidence to formal proof.

Acceptance criteria:

- The proof atlas clearly distinguishes what is now formalized from what remains computational.
- At least one composite theorem joins the current prime-only formal core.
- Lean documentation points directly to the relevant claim IDs.

## Track 6: Full Site Rewrite Around the Registry

Status: `implemented`

Why this matters:

- The site now has a terminology panel and atlas layer, but much of the older document still mixes old framing with new corrections.
- The site should expose the repository’s exact signal, not preserve stale rhetoric.

Todo:

- [x] Rewrite [site/src/components/FiniteReptendDocument.tsx](/Users/mikepurvis/other/quadratic-residue-reptends/site/src/components/FiniteReptendDocument.tsx) around the registry and vocabulary tables instead of handcrafted long-form claims.
- [x] Make theorem status visible wherever the site states a claim.
- [x] Ensure “standard terminology mode” applies across all major explanatory sections, not just the new glossary panel.
- [x] Add dedicated sections for:
  - proof-status atlas
  - counterexample registry
  - composite/CRT story
  - carry-transducer model
  - curated search examples
- [x] Keep the existing local `site/` changes intact unless they directly conflict with the roadmap.

Acceptance criteria:

- A site reader can tell which claims are classical, reproved here, empirical, or open.
- Standard labels appear before aliases throughout the major narrative.
- The site no longer depends on stale handwritten mathematical claims that duplicate the registry.

## Track 7: Registry-Driven Publishing and Sync Tooling

Status: `implemented`

Why this matters:

- The site already reads machine data directly, but some major Markdown docs still duplicate registry content by hand.
- The next hardening gain is to make those outward surfaces generated enough that drift becomes difficult instead of merely detectable.

Todo:

- [x] Add renderer helpers in [bridge_reptends/registry.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/registry.py) for full claim and vocabulary tables.
- [x] Convert [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) and [docs/VOCABULARY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VOCABULARY.md) to registry-backed generated blocks.
- [x] Extend doc-drift tests so those generated blocks are checked against the live registry.
- [x] Add a small sync utility or command for refreshing generated blocks across docs.
- [x] Extend registry-backed generation to at least one more outward surface beyond the proof atlas and vocabulary table.

Acceptance criteria:

- The proof-status table and vocabulary table are derived from registry data, not maintained manually.
- A test fails if either table drifts from the underlying JSON.
- Regenerating public summaries is a documented command rather than a manual edit ritual.

## Track 8: Lean Completion of the Remaining Exact Core Claims

Status: `implemented`

Why this matters:

- The formal core is now substantial, but a few exact claims still rely on Python reduction or classical explanation.
- Completing those claims would make the atlas visibly stronger and tighten the repo’s theorem/prose boundary.

Todo:

- [x] Formalize the global max-over-base-primes preperiod formula building on [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean).
- [x] Generalize the CRT period theorem in [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) from the pairwise core to finite prime-power families.
- [x] Tighten the remaining base-level QR-stride count reduction in [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean).
- [x] Update the atlas and README to distinguish fully formalized claims from partially formalized ones with exact wording.

Acceptance criteria:

- The remaining central exact claims no longer depend on computational reduction for their main theorem-level wording.
- The proof-status atlas can describe the prime, composite, and preperiod core with minimal caveats.

## Track 9: Carry/DFA Theory as a First-Class Layer

Status: `implemented`

Why this matters:

- This is the strongest candidate for distinctive repository value beyond classical reciprocal arithmetic.
- The current transducer layer is useful, but it is still closer to tooling than to a stabilized theory interface.

Todo:

- [x] Expose explicit state graphs, minimization hooks, and equivalence notions in [bridge_reptends/transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py).
- [x] Define the precise relationship between the carry transducer and the long-division DFA.
- [x] Add invariants and canonical examples showing when factorization into orbit plus carry is unique or non-unique at the finite-window/report level without promoting the global claim.
- [x] Promote the carry/DFA open claims into a more explicit local theory roadmap in [docs/CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md).

Acceptance criteria:

- The carry layer is no longer just a demo abstraction; it has explicit mathematical interfaces and invariants.
- Open carry/DFA claims are framed sharply enough to guide proof or counterexample work.

## Track 10: Composite Theory Beyond the Stripped-Core Baseline

Status: `implemented`

Why this matters:

- Composite support is now real, but it still largely reads as “prime story plus stripping.”
- The repo could become unusually strong if composites become a genuine center of gravity.

Todo:

- [x] Add prime-power lifting examples and order-stabilization cases in [bridge_reptends/composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py).
- [x] Separate CRT decomposition, preperiod, and carry phenomena more explicitly in canonical examples.
- [x] Expand [docs/COMPOSITES_CRT.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/COMPOSITES_CRT.md) with family-level statements and counterexamples.

Acceptance criteria:

- Composite examples read as first-class mathematics rather than edge cases.
- The repo has clear example families where the composite structure adds something not visible in the prime case.

## Track 11: Dataset Publication and Larger Reproducible Sweeps

Status: `implemented`

Why this matters:

- The search layer is already useful, but its outputs are still mostly local repo artifacts.
- Publishing stable schemas and larger reproducible sweeps would make the project useful downstream.

Todo:

- [x] Version the example-atlas schema and document it.
- [x] Add larger sweep outputs with reproducible build commands at the atlas/publication layer.
- [x] Separate publication datasets from ad hoc exploratory outputs.
- [x] Surface dataset provenance in docs and search commands.

Acceptance criteria:

- Another reader can regenerate the published datasets without guessing hidden parameters.
- Dataset files are stable enough to serve as references in docs or external notes.

## Track 12: Vocabulary/API Normalization Across Code and CLI

Status: `implemented`

Why this matters:

- Docs and site copy now use standard labels well, but the Python surface still mixes old and new language.
- Standardized terminology should be visible in code-facing entry points too, with aliases preserved as compatibility shims rather than primaries.

Todo:

- [x] Audit [bridge_reptends/__init__.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/__init__.py) exports and key docstrings for alias-first naming.
- [x] Normalize CLI help text and command descriptions around the vocabulary registry.
- [x] Mark legacy names as aliases where the standard label should lead.

Acceptance criteria:

- A new reader can move between docs, site, and code without learning multiple competing naming systems.
- Standard labels become primary in public APIs and CLI output.

## Track 13: Expository Note / Monograph Pass

Status: `implemented`

Why this matters:

- The repo is now closer to a coherent expository package than a loose exploration.
- A short note built from the atlas, counterexamples, and formal theorem inventory would be a stronger public artifact than novelty-forward prose.

Todo:

- [x] Draft a structured note from the registry, vocabulary, canonical examples, and proof-status atlas.
- [x] Distinguish classical background, formalized results, implementation layers, and open questions in a publishable order.
- [x] Reuse the machine-readable data where possible so the note inherits the same source-of-truth discipline as the repo.

Acceptance criteria:

- The repo can produce a concise, high-signal mathematical note without hand-waving or novelty inflation.
- The note’s claims can all be traced back to registry IDs and evidence.

## Phase 3: Open Problems and Formal-System Integration

This phase starts from the repo’s stabilized core rather than from earlier drift and framing issues.

Chosen defaults:

- Agda is treated as a pedagogical/formal companion surface, not as a silent theorem-parity target with Lean.
- The next major mathematical research emphasis is the pair of remaining carry-theory open claims.
- Cross-surface release integration comes after the Agda and carry-theory tracks, not before them.

## Track 14: Agda Proof-Surface Audit and Correspondence

Status: `implemented`

Why this matters:

- Agda is still described as a formal proof layer, but key number-theoretic facts remain postulated.
- There is no authoritative map from Agda postulates to Lean theorems, repo claim IDs, or still-open items.

Todo:

- [x] Inventory every Agda postulate and group it as:
  - locally provable in Agda
  - intentionally postulated but Lean-backed
  - genuinely still open or out of scope
- [x] Add a correspondence table from Agda postulates to Lean theorem names and claim IDs where available.
- [x] Update roadmap wording so Agda is explicitly a pedagogical/formal companion surface, not silently presented as theorem-parity with Lean.
- [x] Add an acceptance note that future public prose must not imply Agda has full proof parity.

Implementation note:

- [docs/AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md) is now the authoritative map for the Agda proof surface and public proof-status wording.

Acceptance criteria:

- Every Agda postulate is classified.
- The roadmap explicitly distinguishes Agda-local proofs from Lean-backed assumptions.
- No future roadmap language treats Agda as theorem-complete unless that changes in a later track.

## Track 15: Agda Pedagogical Core Hardening

Status: `implemented`

Why this matters:

- Agda now has real structure, but too much of the shallow algebraic layer is still postulated.
- The right goal is not full parity; it is to make the Agda layer honest and locally meaningful.

Todo:

- [x] Replace only the shallow, pedagogically important postulates whose proofs do not require deep finite-group machinery.
- [x] Prioritize direct algebraic and structural lemmas such as:
  - conjugacy-style structural lemmas in the orbit/buffer layer
  - modular multiplication and power-distribution lemmas
  - simple example-level definitional facts that are currently postulated
- [x] Explicitly leave deep number-theoretic facts postulated in this track, including:
  - primality abstraction
  - multiplicative-order minimality and divisibility facts
  - Euler-criterion style subgroup results
  - QR-orbit exhaustiveness
- [x] Require examples to annotate which assumptions are local Agda proofs versus Lean-backed postulates.

Implementation note:

- `powMod-mult` is now proved locally in [agda/QRTour/PrimeField.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/PrimeField.agda).
- `neg1-squared-helper` is now proved locally in [agda/QRTour/PrimeField.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/PrimeField.agda).
- `≡ₚ-to-≡-reduced` and `powMod-<p` are now proved locally in [agda/QRTour/Cosets.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/Cosets.agda).
- `repunitRem-closed`, `orbit-buffer-duality`, `shift-conjugacy`, and `noMod-step` are now proved locally in [agda/GeometricStack/OrbitBufferDuality.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/GeometricStack/OrbitBufferDuality.agda), and that module now makes its meaningful assumptions explicit as `b > 0` and `M > 1`.
- [agda/Examples/Prime97.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/Examples/Prime97.agda) and [agda/Examples/Composite96.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/Examples/Composite96.agda) now label local proofs versus Lean-backed assumptions.

Acceptance criteria:

- The remaining Agda postulates are concentrated in genuinely deep number-theoretic areas.
- At least one Agda module becomes materially less postulate-heavy without pretending to solve the whole parity problem.
- The roadmap makes the pedagogical-core boundary explicit.

## Track 16: Exact Carried-Prefix Visibility Threshold Framework

Status: `implemented`

Why this matters:

- `small_k_visibility_threshold` is now the clearest remaining mathematical open claim in the repo.
- The repo has enough infrastructure to sharpen it into a precise research program instead of a vague open question.

Todo:

- [x] Reframe the open claim into exact measurable inputs and outputs:
  - base and block base
  - `q`
  - `k`
  - period data
  - lookahead
  - carried-prefix agreement length
- [x] Add roadmap tasks for:
  - provable lower and upper bounds
  - explicit counterexample search
  - canonical example families (`q = 1`, `q > 1`, same periodic core with different preperiods)
- [x] Require the track to distinguish:
  - exact theorem candidates
  - empirical heuristics
  - counterexample targets

Implementation note:

- [bridge_reptends/visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py) now exposes exact finite-window observables:
  raw-prefix agreement length, first local overflow position, first incoming-carry position, and minimal stabilization lookahead.
- The subproblem `carry_in(j) = floor(qk^(j+1)/(B-k))` and its first-incoming-carry corollary are now implemented exactly, narrowing the remaining open work to lookahead/global visibility behavior.
- Track 16 now also exposes a necessary tail-mass lower bound and an exact finite-window prefix-gap certificate for `lookahead_blocks`, further narrowing the open work to cleaner closed forms and broader global behavior.
- [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md) now states the Track 16 research split explicitly as theorem candidates, heuristics, and counterexample targets.
- The published atlas and CLI now export named visibility case studies and family studies, so progress can be measured by generated examples rather than prose alone.
- Same-core family exports now include cross-base fortification: base `7` exact-law families and base `12` lower-endpoint, upper-endpoint, and exact-law families in one shared coordinate.

Acceptance criteria:

- The roadmap no longer treats the visibility question as a single vague sentence.
- The open claim is broken into exact subproblems that can be proved, falsified, or bounded.
- Progress on the track can be measured by generated examples and counterexamples, not just narrative.

## Track 17: Canonical Carry/DFA Factorization Research Framework

Status: `implemented`

Why this matters:

- `carry_dfa_factorization` remains open, but the repo now has enough carry/remainder machinery to attack it seriously.
- The next step is to sharpen the conjecture before trying to prove the full statement.

Todo:

- [x] Define the candidate notions of factorization explicitly:
  - finite-window agreement
  - graph-level comparison
  - synchronization or morphism candidates
  - global factorization
  - uniqueness versus non-uniqueness
- [x] Add roadmap tasks for bounded counterexample search before theorem promotion.
- [x] Require the track to say what would count as:
  - a theorem
  - a refutation
  - a weaker replacement claim
- [x] Use the canonical cases `21`, `97`, and `996` as the default test family for this track.

Implementation note:

- [bridge_reptends/transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py) now exposes `ObservedStateMap`, `FactorizationDecisionReport`, and `carry_factorization_rows(...)`, so Track 17 works with explicit local notions rather than a single undifferentiated open claim.
- Track 17 now also exposes selector profiles across block widths, making isolated relabeling windows and same-core divergences first-class observable outputs.
- The canonical trio now splits cleanly into regimes: `21` is the trivial `state_relabeling` case, while `97` and `996` are `quotient_candidate_only` cases.
- Selector-profile classification is now systematic enough to live in the published atlas as a research layer, with canonical selector cases, selector families, and grouped same-core disagreement outputs.
- The repo now records bounded counterexamples to naive state relabeling in [data/counterexamples.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/counterexamples.json) and [docs/COUNTEREXAMPLES.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/COUNTEREXAMPLES.md).
- [docs/CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md) now states what would count as a theorem, a refutation, or a weaker replacement claim.

Acceptance criteria:

- The roadmap states a decision-complete research target rather than a vague “study factorization more.”
- The repo would know how to downgrade, split, or restate the claim if counterexamples appear.
- The track is framed as exact theorem and counterexample work, not branding.

## Track 18: Formal-Systems Integration and Release Snapshot

Status: `planned`

Why this matters:

- Once Agda is honest and the carry questions are sharper, the repo needs one coherent cross-surface story again.
- Right now Lean, Agda, docs, atlas data, and the generated note are strong, but their proof-status relationship is not yet a first-class outward artifact.

Todo:

- [ ] Add a roadmap item for a proof-system legend across public surfaces:
  - Lean-formalized
  - Agda-locally-proved
  - Agda-postulated but Lean-backed
  - empirical
  - open
- [ ] Add a release-snapshot task that packages:
  - current proof status
  - open claims
  - published dataset version
  - note generation status
- [ ] Treat this as the release-facing consolidation pass after Tracks 14–17, not before them.

Acceptance criteria:

- A reader can tell what each proof system contributes without reading source files.
- The repo can produce a clean “state of the project” snapshot for branch, release, or paper work.
- This track does not add new math claims; it consolidates the stabilized ones.

## Current State

Tracks 1 through 17 are now implemented. The repo has:

1. registry-backed public claims and vocabulary,
2. a Lean core covering the main exact prime/composite/preperiod statements,
3. explicit carry-vs-remainder finite-state interfaces,
4. family-level composite case studies,
5. a schema-versioned published atlas,
6. standard-label-first API and CLI aliases,
7. a generated expository note,
8. an honest Agda pedagogical core audit,
9. an exact Track 16 visibility framework with cross-base family studies,
10. a Track 17 carry/DFA research framework that separates state relabeling, quotient candidates, and the still-open global theorem.

Track 18 is now the remaining planned release-facing consolidation pass:

1. add the proof-system legend across public surfaces,
2. package the current proof status, open claims, dataset version, and note state into one clean release snapshot.
