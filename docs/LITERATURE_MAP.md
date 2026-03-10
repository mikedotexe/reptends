# Literature Map

This repo is now framed as an expository/tooling layer over standard results. The table below tags each claim family by provenance.

| Source ID | Source | Covers | Claim Tag |
|-----------|--------|--------|-----------|
| `conrad_orders` | [Keith Conrad, *Orders in Modular Arithmetic*](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/ordersmodm.pdf) | multiplicative order, decimal periods, order-of-a-power facts | `classical` |
| `conrad_qr_patterns` | [Keith Conrad, *Quadratic Residue Patterns Modulo a Prime*](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/QuadraticResiduePatterns.pdf) | QR subgroup, cosets, generators of the square subgroup | `classical` |
| `conrad_crt` | [Keith Conrad, *Chinese Remainder Theorem*](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/crt.pdf) | CRT decomposition for composite moduli | `classical` |
| `conrad_qp` | [Keith Conrad, *The p-adic Expansion of Rational Numbers*](https://kconrad.math.uconn.edu/blurbs/gradnumthy/rationalsinQp.pdf) | rational expansions, eventual periodicity, local/global viewpoint | `classical` |
| `leavitt_repeating_decimals` | [William G. Leavitt, *A Theorem on Repeating Decimals*](https://digitalcommons.unl.edu/cgi/viewcontent.cgi?article=1047&context=mathfacpub) | classical repeating-decimal structure and divisor relations | `classical` |
| `allouche_shallit` | [Allouche and Shallit, *Automatic Sequences*](https://www.cambridge.org/core/books/automatic-sequences/B092437A099192BA22DE4CF638142558) | automata/transducer language for numeration systems | `classical background for implemented-here transducer packaging` |

Repo-only tags:

- `reproved-here`: the repo contains a formal theorem or direct proof artifact for a classical statement.
- `implemented-here`: the repo packages a standard viewpoint as a reusable object or dataset.
- `empirical`: observed computationally, explicitly not sold as theorem-level novelty.
