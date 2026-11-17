# Where Did the Pattern Go?

The canonical project for [reptends.mikedotexe.com](https://reptends.mikedotexe.com). Four chapters lead from 1/997's visible powers through carrying and repeating remainders to a mixed-radix run notation. The notation follows three coefficient progressions: powers for 1/997, Fibonacci numbers for 1/9899, and counting for 1/998001. Digit lookup remains an optional supporting tool.

The [notation specification](NOTATION.md) is the compact mathematical and machine-readable reference. The [proof-status atlas](../docs/PROOF_STATUS_ATLAS.md) separates Lean results, implemented conventions, computed examples, and open questions. The [verification record](VERIFICATION.md) identifies the published artifact and its checks.

## Reading path

- **Where did it go?** Addition and carrying explain why 729 becomes 731.
- **Why does it repeat?** Remainders repeat while full powers keep growing.
- **When is it enough?** A 166-digit decimal period is distinct from a 166-group base-1000 loop (498 decimal places).
- **Keep the pattern visible.** Runs show a supplied progression, with one signed balance deciding whether to keep, change, or finish.

`⟨d1,...,dL⟩_B` means L successive digits in radix B. Commas separate positions, the subscript names the radix, and `|` marks a radix change. The first run preserves the ordinary prefix. Each digit's weight uses every radix through that position, including each repeated use inside a run. Leading zeros are positions; they are never dropped.

The general balance is `T=B*r-D*a`. Keep B when `0<=T<D`; zero finishes. For a rejected positive target use `R=floor(D*a/r)+1`. Initial accepted zeros are supported; a rejected zero needs a separate feasibility check. The generator is explicit rather than uniquely determined by the fraction.

## Build and verify

From `essay/`, using the pinned Node 24 dependencies:

```sh
npm ci
npm run typecheck
npm test
npm run build
npm run test:browser
python3 -m unittest discover -s deploy -p 'test_*.py'
```

`BROWSER_ENGINE=firefox` or `BROWSER_ENGINE=webkit` selects another installed Playwright engine. The dedicated `.github/workflows/essay.yml` runs all three engines and the Lean audit. From the repository root, run `python3 lean/check_radix_proofs.py` to build the proofs, verify their source hashes, and audit axioms.

`dist/index.html` is self-contained. `dist/robots.txt` is the only other hosted object. No runtime fonts, scripts, styles, or services are fetched. The main examples and proof references remain readable without JavaScript; controls progressively enhance the static page.

## Source map

- `scripts/render-radices.ts`: notation guide, three-example explorer, completion, and proof map.
- `src/math/progression.ts`: supplied generators and the signed balance state transition.
- `src/math/run-notation.ts`: legal run digits, weighted evaluation, and display labels.
- `scripts/notation-reference.ts`: complete examples and structured notation record.
- `src/run-radices.ts`: exact run and prefix accounting, also used by the optional from-start power explorer.
- `src/math/digit-index.ts`: indexed ordinary digits and independent sequential checks.
- `src/math/lifts.ts`, `unfolded-notation.ts`, and `geometry.ts`: inherited research arithmetic, with provenance and tests. Geometry is retained in source but no longer loaded by the public page.
- `test/`: exact arithmetic, artifact, browser, sharing, accessibility, and offline checks.
- `deploy/`: existing AWS publication workflow; `releases/`: versioned evidence and rollback records.

## Proof and agent context

The HTML embeds two non-executable JSON records. `script#reptends-notation` describes the proposed syntax, positional semantics, generator seeds, complete run digit arrays, first eight changed steps, and exact proof references for all three examples. `script#reptends-certificate` records ordinary cycles, carrying, and endpoints for the earlier four-case verification guide. Both are readable from the static HTML. Arithmetic integers are strings, and explicit indexing and domain restrictions are included. Neither JSON record formally certifies the JavaScript implementation.

Lean's existing run-accounting theorems map digit lists to Horner-packed values and prove preservation across arbitrary valid runs and radix changes. `BalanceRule.lean` proves the decision branches, legal digits, completion, and the infinite value of the written stream, with zero padding after completion. Its stream theorem assumes positive targets after any separately certified initial zero prefix. The glyphs and browser are explanatory implementations of these results. See [NOTATION.md](NOTATION.md) for exact theorem names and limits.

## Shared links

- `?hp=powers`, `?hp=fibonacci`, or `?hp=counting` selects the main progression; `hp_step=1` through `8` selects a changed digit, and `hp_step=0` the final kept step. Example: [Fibonacci's negative balance](https://reptends.mikedotexe.com/?hp=fibonacci&hp_step=2#change-radix).
- `#notation-reference` opens the proof map; `#notation-examples` opens all three inscriptions; `#hp-finish` opens completion.
- `?group=1` through `332` selects the ordinary base-1000 explorer. These are group positions, not decimal positions.
- `?run=1` through `169` retains the optional from-start power construction and its original shared links. This construction has different place weights from the main progression-preserving examples.
- `di_a`, `di_d`, `di_b`, `di_from`, and `di_to` retain the digit-lookup tool's fraction, radix, and range. Positions start at one. Each request emits at most 1,000 digits; independent walking stops at 100,000.

Explorer parameters coexist. Back/Forward restores them, and copy-link buttons have a selectable fallback. Long inscriptions identify omitted intermediate runs explicitly; omitted radices still count in the weights. The structured data never abbreviates its digit arrays.

## Editorial scope and preservation

Version 1.6.0 shortens the opening to 1/997 and removes the square/cube detour, broad polynomial-recurrence derivation, and duplicate general prefix discussion from the live page. It keeps carrying and period context, the three main progressions, optional digit lookup, source references, and the earlier from-start explorer. The old research modules and tests remain in the repository; earlier layouts are preserved in Git and release history.

Human-reader feedback remains pending; [READER-CHECK.md](READER-CHECK.md) records that boundary. The main comprehension check is whether a reader can explain what comes next, what its weight is, and why the radix changes. Automated and AI checks do not substitute for fresh reader feedback.

## Canonical checkout and publication

The public project is `essay/` in `mikedotexe/reptends`. Locally, `/Users/mikepurvis/other/physics-math-research/site` points to `/Users/mikepurvis/other/reptends-publishing/essay`. Original research remains in its existing locations. Publishing uses the existing `reptends` AWS profile and private S3/CloudFront hosting. See [deployment instructions](deploy/README.md). Resource IDs are recorded in `deploy/hosting.json`; credentials stay outside the repository.

Run the arithmetic and browser gates, audit the Lean sources, then publish and verify the exact reviewed artifact. No migration or additional hosted files are needed for the notation reference; its text and structured data are embedded in the page and its standalone specification is public in GitHub.
