# Where Did the Pattern Go?

The canonical website project for [reptends.mikedotexe.com](https://reptends.mikedotexe.com). Five chapters follow the powers inside 1/997: addition and carrying, repeating remainders, the endpoint of a repetend, a changing-radix representation that keeps every power visible as a legal digit, and direct access to a digit by its index. Each chapter has one clear question; full accounting, decimal conversion, proofs, and geometry remain optional.

The [changing-radix chapter](https://reptends.mikedotexe.com/#change-radix) now keeps an already-written prefix, then continues the same visible pattern: tripling for 1/997 and counting for 1/998001. At the first carry, readers compare the ordinary next group with a digit in a new radix, then step through the continuation. The [proof-status atlas](../docs/PROOF_STATUS_ATLAS.md) registers `retained_progression_handoffs` as `reproved-here`: the rule preserves the prefix and the value, with legal positive digits and a remaining tail that tends to zero. The previous from-start power explorer remains in an optional disclosure, with its old links supported.

The [Digit by Index chapter](https://reptends.mikedotexe.com/#digit-index), inspired by Fable’s prototype, jumps to any requested position using modular exponentiation. It supports arbitrary integer bases, nonnegative numerators, improper fractions, ranges, and huge indices. An independent, cancellable long-division walk checks practical distances. The base-1000 group-167 example connects its returning digit `001` to the complete power `3^166` and exact carry balance. The [indexed-digit and carry proofs](../lean/RadixRuns/CarryBridge.lean) establish the formulas; they do not formally verify the browser code.

This project lives in the [`essay/` folder of mikedotexe/reptends](https://github.com/mikedotexe/reptends/tree/main/essay). On Mike's machine, `/Users/mikepurvis/other/physics-math-research/site` is a stable symlink to `/Users/mikepurvis/other/reptends-publishing/essay` in a clean publishing checkout. Both paths reach the same files; the original research checkout and its unfinished changes remain intact.

## Build and check

Use Node 24 or later. Development dependencies are pinned in `package-lock.json`.

```sh
cd essay
npm ci
npm run typecheck
npm test
npm run build
```

The essay artifact is `dist/index.html`; `dist/robots.txt` publishes its open crawler policy. Open the HTML directly in a browser: JavaScript and CSS are inline, all diagrams are SVG, and no runtime dependencies or network requests are needed. Primary-reference links are ordinary optional outbound links. Worked examples and mathematical disclosures remain readable with JavaScript disabled.

For browser checks, install the desired browser through the pinned Playwright development dependency:

```sh
npx playwright install chromium firefox webkit
npm run test:browser
BROWSER_ENGINE=firefox npm run test:browser
BROWSER_ENGINE=webkit npm run test:browser
```

The check runs offline, inspects narrow and wide layouts, exercises the controls and exact states, and writes screenshots under `qa/`. `PLAYWRIGHT_MODULE_PATH` may optionally select an existing Playwright installation. Playwright is a QA tool, not a website runtime dependency. WebKit checks the engine used by Safari; it is not a native Safari application test. The build also rejects external assets and common credential patterns without printing matched secrets.

After publishing, `npm run test:live` (with the same Playwright module setting) checks the public hostname, trusted HTTPS, byte-for-byte artifact match, HTTP redirection, private S3 access, and live interactions.

`node deploy/check-dns.mjs` additionally checks the machine's ordinary DNS, IPv4/IPv6 records, and redirects that preserve shared-group queries. It needs no AWS credentials. The GitHub workflow `.github/workflows/essay.yml` runs arithmetic and browser checks on Linux for Chromium, Firefox, and WebKit; deployment remains a separate local operation.

If a local resolver still caches a pre-launch negative answer, set `REPTENDS_DNS_SERVER=1.1.1.1` for that command. It resolves the real hostname through the selected public resolver and scopes the resulting address to the test process. HTTPS hostname and certificate verification remain enabled; system DNS settings are untouched.

## Source map

- `src/template.html`: semantic essay, static examples, native disclosures, references.
- `src/robots.txt`: an explicit open policy for search, research, and AI crawlers, with a wildcard for future standards-respecting agents.
- `src/opening-examples.ts` and `scripts/render-opening.ts`: exact continuous decimal examples and the aligned power stack, rendered into the HTML at build time and independently checked one decimal digit and one addition column at a time.
- `src/opening.css`: the opening comparison, full-width addition stack, and transition into the 1/997 investigation.
- `src/styles.css` and `src/essay-flow.css`: editorial layout, unified explorer, optional explanations, responsive sizes, focus styles, reduced motion.
- `src/repetition-boundaries.ts`, `scripts/render-boundaries.ts`, and `src/boundaries.css`: exact first-carry, decimal-return, and aligned-word endpoints for 97, 997, 94, and 994; static comparison and shared-position jump controls.
- `src/main.ts`: shared position, ordinary-division readout, optional carry and base-3 views, cycle return, complete integer inspection.
- `scripts/render-verification.ts`: build-time verification guide, independently executable Python checker, and embedded JSON evidence for all four examples.
- `src/decimal-return.ts`: digitwise expansion of the selected exact word, marking all six decimal returns within the two group cycles.
- `src/navigation.ts`: strict group-link parsing and canonical sharing URLs.
- `src/run-radices.ts` and `src/radix-explorer.ts`: exact run accounting and the original from-start 997 power schedule.
- `src/math/progression.ts`, `src/progression-explorer.ts`, `scripts/render-radices.ts`, and `src/progression.css`: preservation of ordinary prefixes, the two continuation examples, optional exact state/weights, and a focused changing-radix comparison.
- `src/math/digit-index.ts`, `src/digit-index-explorer.ts`, `scripts/render-digit-index.ts`, and `src/digit-index.css`: bounded exact input parsing, direct indexed digits, independent sequential checks, query sharing, and the optional power/carry inspector.
- `src/finishing.css`: byline, personal note, and sharing controls.
- `src/geometry.ts` and `src/geometry.css`: ordered pair and triple contributions.
- `src/math/`: preserved exact TypeScript engine; see [arithmetic provenance](src/math/PROVENANCE.md).
- `test/`: inherited arithmetic tests, page-specific contracts, build safeguards, browser checks.
- `deploy/`: resumable AWS tooling, non-secret resource manifest, and [publishing instructions](deploy/README.md).
- `releases/`: versioned publication manifests and preserved verification records.
- [READER-CHECK.md](READER-CHECK.md): a short uncoached human-reader protocol. Human feedback is pending; automated and AI checks do not substitute for it.

## Share a particular moment

The **Copy link to this group** button shares a URL such as [group 8, the 193 follow-up](https://reptends.mikedotexe.com/?group=8#repeat). Group numbers run from 1 through 332. Invalid or ambiguous values fall back to the first change, group 7. Browser Back/Forward restores linked positions, and a selectable field is available if clipboard permission is unavailable. Offline copies still create links to the public essay.

The continuation comparison uses `hp=powers` or `hp=counting`, with `hp_step=1` through `8`. For example, [write 998 in 1/998001](https://reptends.mikedotexe.com/?hp=counting&hp_step=1#change-radix). Steps count positions after the preserved prefix, not decimal places. Other explorer parameters survive selection and Back/Forward restores the state.

Inside **Start with changing units from the beginning**, **Copy a link to this run** shares the independent changing-radix position, for example [run 167, digit 3^166](https://reptends.mikedotexe.com/?run=167#change-radix). Run numbers are 1–169, with exponent `run − 1`; the default is run 4. Invalid or duplicated run parameters use that default. All explorers preserve one another’s query parameters. Their positions refer to different representations and different place weights.

**Copy a link to this result** records the numerator, denominator, base, and one-based position range in `di_a`, `di_d`, `di_b`, `di_from`, and `di_to`. For example, [base-1000 group 167](https://reptends.mikedotexe.com/?di_a=1&di_d=997&di_b=1000&di_from=167&di_to=#digit-index) displays `001`. Each search emits at most 1,000 digits. Positions accept up to 256 decimal digits; numerator, denominator and base accept up to 128. The independent walk stops at position 100,000; direct lookup does not need that walk or a precomputed period. Bases above 36 show each digit’s value in decimal brackets, except base 1000, which shows three-digit groups.

## Mathematical scope

All arithmetic uses `bigint`; only bounded coordinates, indices, and animation timing use ordinary numbers. Growing display widths never change mathematical place values. Every displayed 1/997 step and finite boundary is checked against ordinary division. Initial zero groups in the square and cube are retained.

The expandable **Verify the four examples, by hand or with code** guide states assumptions and indexing, distinguishes local quotient digits from incoming boundary carries, derives the finite balance, and includes an independent Python 3 verifier. The non-executable `script#reptends-certificate` JSON in the built HTML contains complete decimal and grouped cycles, first-carry witnesses, endpoint equations, and finite-prefix accounting. Arithmetic integers are decimal strings; indices and lengths are numbers. The schema version is 1. These are reproducible computations and algebraic derivations, not a proof-assistant certificate.

For 1/997, the minimal decimal period is **166 digits**. A cycle of **166 three-digit groups spans 498 decimal positions**, containing three minimal decimal periods. This corrects the earlier planning description of a 498-digit decimal period.

The “When have we seen enough?” panel distinguishes that first decimal return from the word-aligned return. With groups anchored at the decimal point, digit 166 lies in group 56 (`7 | 00`), associated with `3^55`; the aligned loop ends at group 166 (`667`), associated with `3^165`. Jump buttons reuse the existing position control. The expandable comparison covers 97, 997, 94, and 994, including the initial nonrepeating zero for the two even denominators. Counts start with `k^0 = 1` and describe power positions, not a truncation of the infinite geometric sum. Returning remainders and complete powers remain inspectable without JavaScript.

The proof-status atlas records the [`digit_periodicity`](../docs/PROOF_STATUS_ATLAS.md) quotient step as **reproved-here**. At each selected position, dividing the bounded remainder `r` as `3r = 997d + r′` emits a base-3 digit `d` and next remainder `r′`; the corresponding three-digit decimal word is `r + d`. The interface and tests keep this local quotient digit distinct from the unbounded boundary carry used in the full-power construction.

The [retained-progression claim](../docs/PROOF_STATUS_ATLAS.md) covers the base-invariant rule `R = floor(D*d/r) + 1` for `D > r > 0` and positive desired digit `d`. It gives the smallest radix emitting that digit with a positive remainder, preserves finite prefix accounting, and yields an infinite representation of the same value. The public [handoff module](../lean/RadixRuns/HandoffSearch.lean) includes both worked transitions and the convergence proof. It certifies the mathematics, not the TypeScript implementation.

For 1/997, six ordinary base-1000 digits leave remainder 729. Radices 998, 2992, 8974 then emit 729, 2187, 6561 while retaining remainder 729. For 1/998001, the first 998 ordinary groups are 000 through 997. Radix 999 emits 998 and leaves remainder 999; radices 998002, 999001, 1000000 then emit 999, 1000, 1001. The first radix change decreases the radix. Later radices grow with the displayed values. Each contribution uses the product of every preceding radix, including the unchanged prefix.

The general carry identity, geometric series, and Cauchy products are established mathematics. The unfolded display and marked-run notation are explanatory conventions. The focused mixed-radix library proves arbitrary finite run value preservation, separately certified first returns, and convergence of the power schedule `B_n = D*c^n + 1` for `D > 1, c ≥ 2`. No finite power prefix exhausts its value. These results do not assert a universally preferred representation or formalize the broader recurrence framework. Arbitrary user-entered recurrences, continued fractions, and a general research dashboard remain outside this edition.

## Definition of done for this edition

The essay has a deliberately bounded scope: concrete decimal patterns, exact addition and carrying, repeating remainders, changing measuring units, and indexed access to the same exact arithmetic. A release is ready when its displayed arithmetic is independently checked, its controls and reading path work across supported browsers and screen sizes, its cited Lean run proofs build and pass their axiom audit, and the reviewed standalone artifact is reproducibly published with trusted HTTPS and a private origin.

The editorial acceptance check is a fresh reader who can explain where the extra 2 comes from, what repeats and what grows, what adding nines changes, and why the powers do not stop. Human feedback is still pending; the three independent AI reviews of v1.1.0 are recorded separately in [READER-CHECK.md](READER-CHECK.md). Address specific comprehension failures before expanding the main story.

After acceptance, preserve this edition and maintain it for defects, accessibility, and evidence-backed clarifications. New mathematical questions belong in separate experiments until they earn a place in the essay. The project's completion does not depend on exhausting the research subject or formally verifying the broader recurrence framework.

## Design provenance and preservation

The source arithmetic comes from the chat **! Update recurrence theorem**, developed in September 2026. Its three reused modules remain byte-for-byte copies; provenance and original paths are recorded alongside them. The earlier SVG sketches—unfolded-and-settled, squashing-and-return, square-reciprocal-diagonals, and cubing-a-grid-of-triples—informed the new SVG diagrams. Their original files remain under `/Users/mikepurvis/.codex/visualizations/2026/09/03/01a0659a-3fd3-78c0-b046-acc0eb8562ae/`.

The shared playhead was informed by `/Users/mikepurvis/other/quadratic-residue-reptends`; no files in that project were changed. The original research artifacts and demo are preserved in their existing locations. This directory is the canonical source for the public essay.

## Publishing

After arithmetic and browser QA, publish `dist/index.html` and `dist/robots.txt` through the dedicated `reptends` AWS profile. See [deployment instructions](deploy/README.md). The private S3 origin permits CloudFront access to only those two objects. Resource identifiers are recorded in `deploy/hosting.json`; credentials stay in the local AWS profile.
