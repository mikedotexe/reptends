# Where Did the Pattern Go?

The canonical website project for [reptends.mikedotexe.com](https://reptends.mikedotexe.com). Three continuous decimal expansions—1/97, 1/997, and 1/9997—first show the powers of three giving way to a jumble of digits and identify the last clean power in each. The essay then stacks full-width powers to recover the changed groups through ordinary addition and follows 1/997 into a finite remainder loop with synchronized base-3 and three-digit decimal readouts. Square/cube geometry remains an optional continuation.

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
- `src/styles.css`: editorial layout, responsive sizes, focus styles, reduced motion.
- `src/repetition-boundaries.ts`, `scripts/render-boundaries.ts`, and `src/boundaries.css`: exact first-carry, decimal-return, and aligned-word endpoints for 97, 997, 94, and 994; static comparison and shared-position jump controls.
- `src/main.ts`: shared position, carry split, synchronized base-3/base-1000 readouts, cycle return, complete integer inspection.
- `src/navigation.ts`: strict group-link parsing and canonical sharing URLs.
- `src/finishing.css`: byline, personal note, and sharing controls.
- `src/geometry.ts` and `src/geometry.css`: ordered pair and triple contributions.
- `src/math/`: preserved exact TypeScript engine; see [arithmetic provenance](src/math/PROVENANCE.md).
- `test/`: inherited arithmetic tests, page-specific contracts, build safeguards, browser checks.
- `deploy/`: resumable AWS tooling, non-secret resource manifest, and [publishing instructions](deploy/README.md).
- `releases/`: versioned publication manifests and preserved verification records.
- [READER-CHECK.md](READER-CHECK.md): a short uncoached human-reader protocol. Human feedback is pending; automated and AI checks do not substitute for it.

## Share a particular moment

The **Copy link to this group** button shares a URL such as [group 8, the 193 follow-up](https://reptends.mikedotexe.com/?group=8#carry). Group numbers run from 1 through 332. Invalid or ambiguous values fall back to the first change, group 7. Browser Back/Forward restores linked positions, and a selectable field is available if clipboard permission is unavailable. Offline copies still create links to the public essay.

## Mathematical scope

All arithmetic uses `bigint`; only bounded coordinates, indices, and animation timing use ordinary numbers. Growing display widths never change mathematical place values. Every displayed 1/997 step and finite boundary is checked against ordinary division. Initial zero groups in the square and cube are retained.

For 1/997, the minimal decimal period is **166 digits**. A cycle of **166 three-digit groups spans 498 decimal positions**, containing three minimal decimal periods. This corrects the earlier planning description of a 498-digit decimal period.

The “When have we seen enough?” panel distinguishes that first decimal return from the word-aligned return. With groups anchored at the decimal point, digit 166 lies in group 56 (`7 | 00`), associated with `3^55`; the aligned loop ends at group 166 (`667`), associated with `3^165`. Jump buttons reuse the existing position control. The expandable comparison covers 97, 997, 94, and 994, including the initial nonrepeating zero for the two even denominators. Counts start with `k^0 = 1` and describe power positions, not a truncation of the infinite geometric sum. Returning remainders and complete powers remain inspectable without JavaScript.

The proof-status atlas records the [`digit_periodicity`](../docs/PROOF_STATUS_ATLAS.md) quotient step as **reproved-here**. At each selected position, dividing the bounded remainder `r` as `3r = 997d + r′` emits a base-3 digit `d` and next remainder `r′`; the corresponding three-digit decimal word is `r + d`. The interface and tests keep this local quotient digit distinct from the unbounded boundary carry used in the full-power construction.

The general carry identity, geometric series, and Cauchy products are established mathematics. The unfolded display notation and this explanatory sequence are an exploratory presentation, not a claim to a new division algorithm or a formally verified general theorem. Arbitrary recurrence inputs, mixed radices, continued fractions, and the full research dashboard remain outside this first version.

## Design provenance and preservation

The source arithmetic comes from the chat **! Update recurrence theorem**, developed in September 2026. Its three reused modules remain byte-for-byte copies; provenance and original paths are recorded alongside them. The earlier SVG sketches—unfolded-and-settled, squashing-and-return, square-reciprocal-diagonals, and cubing-a-grid-of-triples—informed the new SVG diagrams. Their original files remain under `/Users/mikepurvis/.codex/visualizations/2026/09/03/01a0659a-3fd3-78c0-b046-acc0eb8562ae/`.

The shared playhead was informed by `/Users/mikepurvis/other/quadratic-residue-reptends`; no files in that project were changed. The original research artifacts and demo are preserved in their existing locations. This directory is the canonical source for the public essay.

## Publishing

After arithmetic and browser QA, publish `dist/index.html` and `dist/robots.txt` through the dedicated `reptends` AWS profile. See [deployment instructions](deploy/README.md). The private S3 origin permits CloudFront access to only those two objects. Resource identifiers are recorded in `deploy/hosting.json`; credentials stay in the local AWS profile.
