# Counterexample Registry

This file records concrete failures of older prose so the same mistakes do not come back in later drafts or UI copy.

| Legacy Claim | Counterexample | What Actually Happens | Replacement Statement |
|--------------|----------------|-----------------------|-----------------------|
| Raw blocks are always `1, k, k^2, ...` | `N = 37`, base `10`, `m = 3` | `1000 = 27*37 + 1`, so the exact coefficients are `27, 27, 27, ...` | Use `1/N = q/(B-k) = Σ qk^j / B^(j+1)` and reserve literal `k^j` for `q = 1` |
| Full reptend implies all even QR strides | `p = 19`, base `10` | Exact strides are `[2, 4, 8, 10, 14, 16]`, not every even number | For full reptend, strides are `m = 2u` with `gcd(u, (p-1)/2) = 1` |
| Half reptend implies all consecutive QR strides | `p = 31`, base `10` | Exact strides are `[1, 2, 4, 7, 8, 11, 13, 14]`, not `1..15` | For half reptend, strides are exactly the `m` coprime to `(p-1)/2` |
| Any small `k` gives a good coordinate | `N = 37`, base `10`, `m = 1` | Here `B = 10 < 37`, so `q = 0` and the coordinate is not yet useful | Require `B > M` so `q > 0` before calling a mode “good” |
| Visible mismatch begins exactly at local overflow | `N = 97`, base `10`, `m = 2` | Local overflow is at `j = 5`, but incoming carry already changes block `j = 4` | Use `carry_in(j) = floor(qk^(j+1)/(B-k))` and compare incoming carry to the local overflow boundary |
| Positive `q` does not affect incoming-carry timing | `N = 249`, base `10`, `m = 3` | Local overflow is at `j = 4`, but positive-`q` tail carry already appears at `j = 3` | Incoming carry depends on the full tail `qk^(j+1)/(B-k)`, not only on local coefficient size |
| Matching displayed words implies simple state relabeling | `N = 97`, base `10`, `m = 2` | Outputs match, but carry state `0` aligns with remainder states `{1, 3, 9, 27}`, so state relabeling already fails on the observed window | Separate finite-window word agreement, quotient candidates, and global factorization |
| Stabilized composite outputs imply trivial state relabeling | `N = 996`, base `10`, `m = 3` | Outputs match, but carry state `0` aligns with remainder states `{1, 4, 16, 64}`, so the composite/preperiod case remains quotient-like | Treat composite carry/DFA comparisons as tests of specific state-map notions, not as evidence of unique factorization |
| Larger block widths preserve state relabeling once it appears | `N = 21`, base `10`, `m = 6` then `m = 7` | The selector profile is `finite_word_only -> state_relabeling -> finite_word_only`, so the relabeling window is isolated and nonmonotone in `m` | Track selector profiles explicitly; regime changes must be stated with respect to `m`, not assumed monotone |
| Selector profile depends only on the stripped periodic core | `249` versus `996`, base `10` | `249` has an isolated `state_relabeling` window at `m = 6`, but same-core `996` stays `quotient_candidate_only` across its tested modes | Treat selector profiles as properties of the actual denominator and chosen coordinate family, not of the periodic core alone |
| Doubling a denominator only shifts relabeling windows predictably | `17` versus `34`, base `10` | `17` has relabeling only at `m = 5`, while `34` keeps `m = 5` and gains another relabeling window at `m = 7` | Treat selector profiles as family objects. Small-multiple moves can preserve and enlarge relabeling windows, not just shift or destroy them |

Machine-readable backing lives in [counterexamples.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/counterexamples.json).
