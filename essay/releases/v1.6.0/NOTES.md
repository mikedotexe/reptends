# Read the progression in runs — v1.6.0

The changing-radix chapter now uses one notation throughout: angle brackets contain successive digits using a shared radix, commas preserve positions, and bars mark radix changes. The three main examples retain their original prefixes and continue tripling (1/997), Fibonacci (1/9899), or counting (1/998001). The run before the first switch is selectable; later excerpts explicitly identify omitted runs whose radices still count toward the weights.

A short reading guide leads into the explorer. Readers can open all three inscriptions together, inspect weights, or use a compact proof map. Zero completion is retained as `1/8 = 0.⟨1,2,5⟩_10`. The older from-start power explorer and its shared links remain available in a disclosure, using the same symbols.

The standalone `essay/NOTATION.md` specifies syntax, weights, generators, the balance policy, completion, indexing and scope. A non-executable `script#reptends-notation` record embeds complete run digits and eight changed steps for all three examples, plus the rule and theorem references. Arithmetic integers are decimal strings; no digit arrays are abbreviated. Existing ordinary-cycle evidence remains separate.

The proof map connects the convention to the already registered `mixed_radix_run_value_preservation` and `unified_balance_rule` claims. No Lean source or theorem was changed. The glyphs, serializer, complete initial prefix computations and browser remain independently tested implementations, not formally verified programs.

The live reading path is shorter: the opening focuses on 1/997, the square/cube geometry section is removed, and the broad polynomial-recurrence and duplicate finite-prefix digressions are removed. Digit lookup is labeled as an optional tool after the main conclusion. Research sources, arithmetic modules, earlier shared links and release history are preserved.

Publication evidence is recorded alongside these notes after the release checks pass.
