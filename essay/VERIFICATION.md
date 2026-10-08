# Verification — essay v1.0.3

Published 8 October 2026 (Pacific time). The standalone artifact is 95,420 bytes, SHA-256 `c07acf1c4bdffac170b4a9f3a61aa5cf7b23fcb0370322305fbe82b8e5536a4e`. The tested source commit is [`9ef7d7f`](https://github.com/mikedotexe/reptends/commit/9ef7d7f14ea683c0199d25a5ca4987a5d5f56513). Later release-record commits do not change the built page.

## Continuous decimals and the stopping point

The introduction prints sixteen groups each of 1/97, 1/997, and 1/9997 as continuous decimal digits without inserted spaces. Color, outlines, faint block shading, and text labels identify the ×3 prefix, its first changed group, and the later “number salad.” The page explicitly identifies the last exact ×3 values as `27 = 3³`, `243 = 3⁵`, and `2187 = 3⁷`; the first corrections remain 81 → 83, 729 → 731, and 6561 → 6562.

Independent digit-by-digit long division checks every printed digit, including leading zeros. The examples are rendered into the standalone HTML at build time and remain readable without JavaScript.

## Full-width addition stack

The new 1/997 stack writes powers 3⁴ through 3¹¹ at their fixed decimal places while retaining all of their base-1000 words. In particular, `2187` occupies `002 | 187`. Direct column addition reproduces the first five changed groups:

- `729 + 002 = 731`
- `187 + 006 = 193`
- `561 + 019 = 580`
- `683 + 059 = 742`
- `049 + 177 = 226`

The final displayed column retains the remaining `147` from `177147` and shows an ellipsis instead of claiming a completed decimal total without the next power. Exact tests reconstruct every displayed whole power from its aligned words and independently verify every completed column against ordinary division.

## Arithmetic and browser verification

All 44 arithmetic, artifact, and navigation tests pass, along with strict TypeScript checking and the standalone build. The three inherited arithmetic modules remain unchanged. All 332 interactive positions and 333 finite boundaries retain their exact checks; the minimal decimal period remains 166 digits, while 166 three-digit groups span 498 decimal positions.

Local Chromium 151 and WebKit 26.5 full suites passed against the exact published artifact. Visual checks cover 320, 360, 768, and 1440 px; the narrow stack has an explicit swipe cue, keyboard focus, and verified access to its last column. The suites also cover JavaScript-disabled reading, reduced and normal motion, large integers, geometry, shared links and history, clipboard fallback, and the absence of external asset requests or browser errors.

[GitHub browser checks passed](https://github.com/mikedotexe/reptends/actions/runs/37810175329) on Ubuntu 24.04 for Chromium, Firefox, and WebKit. Every job passed all 44 tests, typechecking, the 95,420-byte build, and its browser suite. WebKit covers Safari's engine rather than the native Safari application; Linux CI supplies Firefox coverage because the local Firefox build cannot start on this macOS version.

## Publication

The narrowed deployer uploaded only `index.html`, and CloudFront invalidation completed. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` passed: ordinary DNS resolves; trusted HTTPS serves the exact reviewed artifact at `/`, `/index.html`, and `/?group=8`; HTTP returns 301 to HTTPS while preserving the query; anonymous S3 access returns 403; and live controls work without additional asset requests or browser errors.

Current resource IDs and publication evidence are in `deploy/hosting.json` and `deploy/live-verification.json`. The release manifest is `releases/v1.0.3/manifest.json`.

## Outstanding evidence

Fresh-reader feedback remains pending; the protocol is in [READER-CHECK.md](READER-CHECK.md). Automated or AI checks do not substitute for human comprehension evidence. The older repository CI has unrelated, pre-existing Yarn bootstrap and generated-documentation failures, documented in the [v1.0.1 verification record](releases/v1.0.1/VERIFICATION.md); this change does not modify that research code or workflow.
