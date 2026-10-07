# First-release verification — 6 October 2026

Reviewed artifact: `dist/index.html`, 64,812 bytes.

SHA-256: `ceb9acdf01c7588b469a02a6361f74f648b36865248c6f13a6a1ad3758ac0ce6`

## Arithmetic and build

- `npm run typecheck`: passed.
- `npm test`: 36 tests passed, including all 332 displayed 1/997 steps against independent ordinary division and all 333 finite boundaries.
- The first correction is 729 + 2 = 731. The following group is 2187 + 6 − 1000 × 2 = 193.
- Remainder/output return after 166 three-digit groups. Their 498 decimal positions contain three minimal 166-digit decimal periods.
- Square/cube coefficients and ordered contribution counts pass; one/two initial zero groups are preserved. Carrying is explicitly separate from collecting coefficients.
- Three copied arithmetic modules match their original research sources byte-for-byte.
- Build emits one HTML file with inline CSS/JavaScript and SVG diagrams. Artifact checks reject external resources and common credential patterns.
- Deployment tooling: seven tests passed, covering publication gates, resumability, preservation of other credential profiles, and the live-verification gate for permission reduction.

## Browser acceptance

Automated checks used Chromium through Playwright, loading the file with the network offline:

- 320, 360, 768, and 1440 px viewports, with light and dark system preferences.
- All 332 UI positions checked against the exact engine; boundary positions repeated across viewport sizes.
- Reveal, Previous/Next, First change, and forward/backward cycle interactions.
- Keyboard range changes, rotation controls, and native disclosures.
- Every square/cube slice, initial zero groups, transformed diagrams, and coefficient counts.
- Reduced motion; normal animation movement, completion, restart, and cancellation when the main selection changes.
- All disclosures open at the largest integer on a 320 px screen, with no horizontal page overflow.
- No JavaScript: examples, geometry prose, and native disclosures remain readable; inactive controls are hidden.
- No browser errors and no external resource requests.

Full-page screenshots and viewport crops are under `qa/`. Desktop, tablet, phone opening, and large-integer views were visually inspected. Browser coverage is Chromium; other browser engines have not been separately tested.

## Publication

The deployment manifest `deploy/hosting.json` records resource identifiers, uploaded artifact hash, invalidation, and DNS changes. The deployment guide records the checks and permission reduction after live verification. No credentials are included in either record.

Live checks passed: valid HTTPS at `/` and `/index.html`, exact artifact SHA-256, HTTP 301 to HTTPS, and anonymous S3 access denied with 403. Authoritative Route 53 nameservers, Cloudflare DNS, and Google DNS resolve the A/AAAA aliases. The machine's default resolver initially retained its pre-launch negative answer; live verification used a process-scoped public DNS lookup with the true hostname, Host header, SNI, and certificate validation retained.

`npm run test:live` passed over the public site: reveal 731, next group 193, reset, 166-group return with the enlarged 83-digit power, and the cube face view. There were no additional asset requests or browser errors. The live desktop viewport was also inspected in `qa/live-desktop.png`.

After live verification, the administrator attached `ReptendsPublish` and detached `ReptendsBootstrap`. The deployer now has only uploads to this bucket's `index.html` and invalidation creation/status for the one distribution. Nine effective IAM permission checks passed, including denials for other objects, other distributions, DNS edits, and IAM changes. The narrowed profile successfully read the completed invalidation. Evidence is in `deploy/publisher-effective-permissions.json` and the deployment manifest.
