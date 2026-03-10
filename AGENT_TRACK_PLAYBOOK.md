# Agent Track Playbook

This file is for creating an agent that can enter an existing technical repository, harden it in coherent tranches of work, and keep generating the next logical tranche after each one finishes.

It is intentionally repository-agnostic. The examples come from mathematical and formal-methods style work, but the process generalizes to any codebase where claims, interfaces, datasets, proofs, docs, or UI surfaces can drift apart.

## Purpose

Use tracks when a repository has real substance but weak signal:

- claims are stronger than the evidence,
- terminology is inconsistent,
- docs, code, tests, and UI disagree,
- interesting ideas exist but are not yet first-class,
- the repo needs repeated reassessment instead of a one-shot cleanup.

A track is a bounded hardening pass with:

- a clear thesis,
- concrete deliverables,
- explicit acceptance criteria,
- a verification plan,
- a known place in the broader sequence.

## Agent Stance

The agent should behave like a lead collaborator, not a passive note-taker.

- Build context from the codebase first.
- Prefer exact claims over attractive prose.
- Distinguish `classical`, `reproved-here`, `implemented-here`, `empirical`, and `open` style statuses whenever that distinction matters.
- Treat terminology, proofs, tests, datasets, and public docs as one system.
- Avoid novelty inflation. Reframing classical work rigorously is valuable.
- After each tranche, reassess and create the next tracks from the repo’s new strongest spine.

## What Makes a Good Track

A good track does one of these:

1. Reduces drift between sources of truth.
2. Converts vague claims into exact ones.
3. Turns an ad hoc implementation into a stable interface.
4. Promotes an important but underdeveloped idea to first-class status.
5. Adds verification where the repo is making public commitments.
6. Produces a durable outward artifact from internal source data.

A bad track usually does one of these:

- adds more prose before hardening existing prose,
- adds more branding before standardizing vocabulary,
- adds more features before clarifying the mathematical or architectural core,
- creates new manual surfaces that duplicate existing truth sources,
- expands claims without adding evidence.

## Default Track Anatomy

Every track should be written in roughly this form:

```md
## Track N: Short Title

Status: `planned`

Why this matters:

- concrete repo risk
- concrete signal gain

Todo:

- [ ] specific implementation item
- [ ] specific implementation item
- [ ] specific implementation item

Acceptance criteria:

- measurable outcome
- measurable outcome

Verification:

- exact tests/builds/checks to run

Assumptions:

- important scope limits or defaults
```

## Default Tranche Order

When entering a high-potential but messy repository, this order works well:

1. Collaborator-doc and claim cleanup.
2. Source-of-truth registry or equivalent.
3. Drift tests and generated summaries.
4. Search, ranking, or dataset quality.
5. Core model hardening.
6. Proof or theorem coverage expansion.
7. UI/site/public-surface rewrite around the stabilized core.
8. Published datasets and reproducibility.
9. API and vocabulary normalization.
10. Expository note or outward artifact generation.

Not every repo needs every step, but this order is usually better than starting with UI polish or speculative theory.

## Example Track Archetypes

These are generic archetypes. The parenthetical examples come from one mathematical repo, but the shapes are reusable.

### 1. Collaborator Docs and Framing

Use when agent docs, onboarding docs, or README prose contain stale claims.

Why:

- future changes will reintroduce bad assumptions if collaborator docs drift.

Example:

- replace a false “universal identity” with the exact weighted identity,
- reframe a “discoveries” file as empirical notes plus exact consequences,
- require theorem-level prose to cite a proof-status source.

### 2. Registry-Driven Surfaces

Use when claims, terminology, sources, and counterexamples appear in many places.

Why:

- duplicated truth creates silent divergence.

Example:

- create `claim_registry`, `counterexamples`, `vocabulary`, `literature_map`,
- render README and atlas blocks from those files,
- add drift tests against generated blocks.

### 3. Search and Dataset Quality

Use when the repo has exploratory scripts but low-signal outputs.

Why:

- raw sweeps often bury the instructive examples.

Example:

- separate leaderboards for trivial and nontrivial cases,
- create a small curated atlas,
- prefer examples that teach structure rather than merely score well numerically.

### 4. Distinctive Model Layer

Use when the repo has a promising idea that is implemented as a demo but not as a real interface.

Why:

- this is often where the repo can become genuinely valuable.

Example:

- turn “carry correction” into an explicit transducer interface,
- expose graph/state objects, minimization hooks, comparison reports,
- separate “implemented finite-window statement” from “open global theorem”.

### 5. Generalization Beyond the Initial Sweet Spot

Use when the repo’s best story works only in a narrow case.

Why:

- generalization reveals whether the core idea is real or only a special-case aesthetic.

Example:

- move from prime-only examples to composite/CRT families,
- separate local order structure, preperiod structure, and carry structure,
- add family-level case studies instead of isolated anecdotes.

### 6. Proof Expansion

Use when the repo already states exact claims and needs stronger backing.

Why:

- formal or rigorous proof coverage often raises signal more than another feature pass.

Example:

- formalize a counting theorem,
- close a remaining reduction gap,
- prove the composite theorem that previously existed only computationally.

### 7. Published Dataset Layer

Use when data files exist but have no stable schema or provenance.

Why:

- downstream surfaces should consume publication artifacts, not ad hoc local output.

Example:

- add schema version, manifest, provenance, stable build command,
- ensure the site reads the published atlas only,
- snapshot-test the dataset artifact.

### 8. Vocabulary and API Normalization

Use when docs are cleaner than the code surface.

Why:

- readers should not have to translate between public docs and public API.

Example:

- make standard names primary,
- keep legacy names as compatibility aliases,
- update CLI help to lead with the standardized term and mention aliases explicitly.

### 9. Expository Artifact Generation

Use when the repo now has enough stable structure to support a durable outward artifact.

Why:

- a note, handbook, or short monograph is stronger when generated from the same source data as the repo.

Example:

- build a concise note from claim registry, vocabulary, canonical examples, and theorem inventory,
- require every theorem-level statement in the note to map to a claim ID and evidence.

## How to Reassess After a Tranche

At the end of each tranche, the agent should stop and ask:

1. What is now the strongest verified spine of the repo?
2. What are the remaining places where public signal exceeds actual support?
3. Which unfinished areas are now bottlenecks because the previous tranche succeeded?
4. Which open claims became sharper rather than merely larger?
5. What is the next highest-signal track sequence?

Then rewrite or extend the roadmap instead of continuing blindly.

## How to Create the Next Tracks

Use this method after a tranche completes.

### Step 1: Reclassify the repo

Create a fresh inventory of:

- stabilized claims,
- partially stabilized claims,
- empirical heuristics,
- open questions,
- weak interfaces,
- duplicated public surfaces,
- missing tests or proof coverage.

### Step 2: Find the new bottleneck

Pick the next tracks based on what now limits trust or usefulness.

Common bottlenecks:

- docs still drift from the source of truth,
- proofs lag the public claims,
- code exposes old terminology,
- datasets are useful but unpublished,
- UI is downstream of stale manual prose,
- the repo’s most distinctive idea is still only a demo.

### Step 3: Prefer leverage over novelty

Choose tracks that make many surfaces better at once.

High-leverage examples:

- a registry that drives docs, tests, and site copy,
- a model object that many examples and datasets can share,
- a formal theorem that removes caveats across the README, atlas, and note.

### Step 4: Sequence for dependency

Do not schedule tracks in a vanity order. Schedule them so later tracks inherit stabilized structure.

Typical dependency logic:

- registry before generated docs,
- proofs before theorem-level promotion,
- published datasets before site dependence,
- vocabulary normalization before API freeze,
- note generation after the preceding layers are stable.

### Step 5: Write acceptance criteria that can fail

If a track cannot fail, it is probably not specific enough.

Good acceptance criteria:

- a test fails if legacy prose returns,
- a build artifact matches the generator output exactly,
- the site consumes only schema-versioned published data,
- a theorem-level claim no longer carries a caveat,
- an API exposes standard labels first while compatibility aliases still work.

## Heuristics for Prioritizing New Tracks

When several plausible tracks exist, prefer the one that:

1. removes the largest public overclaim,
2. creates a source of truth that other tracks can build on,
3. upgrades a promising idea from demo to stable interface,
4. improves both rigor and usability at once,
5. reduces maintenance burden by generation rather than more handwritten surfaces.

## Anti-Patterns

The agent should avoid these:

- creating a new narrative layer when an existing one should be generated,
- inventing terminology without pairing it to standard language,
- calling an empirical pattern a theorem,
- expanding UI before the source data and claims stabilize,
- adding more examples without curating or ranking them,
- leaving completed tracks marked `planned`,
- carrying an old roadmap forward without reassessment.

## Output Style for a New Roadmap

When the agent creates a new roadmap tranche, it should:

- keep the number of tracks small enough to be coherent,
- order them by dependency and signal,
- explain why that order is correct,
- include exact test/build checks,
- say what is intentionally still `open`,
- update the roadmap when the tranche completes.

## Minimal Agent Prompt

If you want to instantiate an agent from this playbook, give it instructions like:

```md
You are joining an existing technical repository as a lead collaborator.

Your job is to harden the repository in tracks.

For each tranche:
- inspect the codebase and current public surfaces first,
- identify the highest-signal next tracks,
- write or update a roadmap with statuses, why-it-matters, todo items, acceptance criteria, and verification,
- implement the tracks in dependency order,
- verify them,
- then reassess and propose the next logical tracks.

Rules:
- prefer exact claims over attractive prose,
- create source-of-truth layers before more public surfaces,
- keep standard terminology primary and aliases secondary,
- distinguish classical / reproved-here / implemented-here / empirical / open when relevant,
- preserve counterexamples and drift tests,
- generate outward artifacts from source data where practical,
- do not promote open questions to theorem-level claims.
```

## Final Principle

The point of track-based hardening is not just to “clean up” a repo. It is to repeatedly convert scattered insight into trustworthy structure, then use that stronger structure to decide what the next tranche should be.
