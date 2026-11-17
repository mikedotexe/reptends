# Essay v1.3.0 — Digit by Index

Chapter 05 adds direct access to a fractional digit in any integer base. The reader chooses a fraction, base, and one-based position or range. Modular exponentiation jumps to the incoming remainder; one division step reads its digit. An independent, cancellable long-division walk checks the result for positions up to 100,000. Huge indices do not require a period search or the preceding digits.

The interaction adapts Fable’s “Digit by Index” prototype, provided by Mike. The original attachment is preserved separately, with SHA-256 `aa90e514ed9775811e0a6c036aee14dd3b1e50c7419cb5d32b53dfa50b06c4f6`. The adaptation uses exact BigInt values for arbitrary bases, bounded parsing and ranges, explicit stale-result handling, cancellation, shareable positions, and a selectable clipboard fallback. It introduces no external assets or runtime dependencies.

The 1/997 group-167 preset shows the returning base-1000 digit `001` together with the growing power `3^166`, its quotient and incoming boundary carry. The exact balance connects ordinary digits to the retained powers. The neighboring changing-radix chapter keeps its distinct weights and construction. Non-1 numerators, improper fractions, terminating expansions, and bases above 36 have explicit display conventions.

The public Lean library now includes generic indexed remainder/digit identities and the phase11 carry bridge: 23 source-hash checks and 149 theorem axiom checks. The proof-status atlas registers the new claim family. These proofs establish the formulas; the browser implementation is checked by tests rather than formally verified.

Release checks cover strict TypeScript, 87 Node tests, 13 deployment-safety tests, local Chromium and WebKit, mobile and desktop screenshots, offline operation and a no-JavaScript worked example. Linux Chromium, Firefox, WebKit and Lean CI, followed by trusted-HTTPS live checks, gate publication. See the final manifest and receipts for their recorded outcomes. Human-reader feedback remains pending.
