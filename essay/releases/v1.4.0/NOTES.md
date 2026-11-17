# Keep the progression visible — v1.4.0

Chapter 04 now begins with two concrete continuations, each preserving the ordinary base-1000 prefix before carrying obscures the selected progression.

- **1/997:** keep 001,003,009,027,081,243; use radix998 to write729, then2992 to write2187.
- **1/998001:** keep000 through997; use radix999 to write998, then998002 to write999. Subsequent digits continue1000,1001,… .

Radices and digit values are separate; every digit has weight one divided by the product of all radices so far. Ordinary notation retains the exact value. This alternative keeps the identified progression visible with changed weights.

The prior from-start power schedule remains available in a disclosure, including existing `?run=` links. The general rule and exact accounting are optional. The main chapter remains readable without JavaScript.

The mathematical source is phase13, preserved at `physics-math-research/research/reptend-bases/phase13`. `lean/RadixRuns/HandoffSearch.lean` preserves its 50 statements and proof bodies unchanged. The atlas registers the scope as `retained_progression_handoffs`; this is mixed-radix value accounting, with no novelty or uniqueness claim and no formal verification claim for the browser code.

Publication evidence is recorded in the accompanying manifest and verification receipt once release gates pass.
