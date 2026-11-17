# Verification — essay v1.2.0

Published 16 November 2026 (Pacific time) at [reptends.mikedotexe.com](https://reptends.mikedotexe.com/#change-radix).

- Reviewed source: [`53d39f4`](https://github.com/mikedotexe/reptends/commit/53d39f43bb2c243ebceae39add6ac741135f2374).
- `index.html`: 154,908 bytes, SHA-256 `b8e14bd41cdffcfe55b0fd0d76ae1fd764d7a90e2c9610fc9c04052136fa3954`.
- `robots.txt`: 613 bytes, SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Release CI](https://github.com/mikedotexe/reptends/actions/runs/44019108921) passed Chromium, Firefox, WebKit, and the new Lean build/audit job.

## Reading path

Four numbered chapters follow carrying, remainders, finite descriptions, and changing radices. The new chapter has one explorer and four short takeaways. Decimal conversion, exact state, and general proofs are native optional disclosures. Introductions and transitions are shorter; fixed-radix repetition is explicitly distinguished from changing the next radix.

The construction retains 1/997 while choosing radix 997·3^n+1 and emitting digit 3^n. Each bar is a one-digit first return to remainder 1. Long integers are abbreviated in the main view, with every exact digit available in the inspector. Run links are independent of group links and support Back/Forward and a selectable clipboard fallback.

## Arithmetic and proof checks

Strict TypeScript, 76 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. The new tests independently compare all 169 displayed runs to division of the accumulated product. They check exact residuals, other denominators and multipliers, multi-digit runs, changing radices, termination, first returns, decimal truncation and link bounds.

`python3 lean/check_radix_proofs.py` builds the public proof library, verifies 22 unchanged imported source hashes, and audits 136 declarations. Dependencies are subsets of `propext`, `Classical.choice` and `Quot.sound`. No unfinished proofs, custom axioms, `native_decide` or kernel-check bypasses occur in these sources. Both public claim families are registered in the proof-status atlas.

Browser CI covers the existing explorer, powers at positions 166–168, exact inspector values, independent sharing/history, keyboard controls, reduced and ordinary motion, no-JavaScript examples, offline operation, and widths down to 320 pixels. Mobile and desktop screenshots were inspected, including the compact large-power view. Local Chromium and WebKit passed; Firefox's local macOS headless process failed to initialize, and its Linux release job passed.

## Live publication

CloudFront invalidation `IEWXW61OAWLASUJPF63PF7GQKE` completed. `python3 deploy/aws_site.py verify --target live`, `npm run test:live`, and `node deploy/check-dns.mjs` passed. Additional requests to `?run=167` and `?group=8&run=169` served the exact reviewed HTML. Public proof sources and the atlas returned successfully.

Trusted HTTPS serves the recorded bytes. HTTP redirects preserve the tested group query; ordinary IPv4/IPv6 DNS resolves. The crawler policy is unchanged, and anonymous S3 access to both objects returns 403. The live browser checked the new radix and power at exponent 166 and the following power, alongside inherited interactions, with no extra asset requests or runtime errors.

The [manifest](releases/v1.2.0/manifest.json), [live receipt](releases/v1.2.0/live-verification.json), and [CI receipt](releases/v1.2.0/ci.json) preserve the evidence. The [v1.1.1 verification](releases/v1.1.1/VERIFICATION.md) and prior source commit remain available for rollback.

## Evidence boundaries

Fresh human-reader feedback remains pending. The broader repository's generated-documentation drift was observed before these registry edits. The dedicated essay workflow is this release's gate. The bracket/bar typography is explanatory notation; the underlying records and arithmetic are formalized. The broader recurrence framework's open claims are unchanged.
