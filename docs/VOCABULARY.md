# Standardized Vocabulary

Preferred practice: use the standard label first, and mention repo aliases only as secondary explanatory names.

<!-- VOCABULARY_TABLE_START -->
| Vocabulary ID | Preferred Label | Repo Alias | Exact Meaning | Scope |
|---------------|-----------------|-----------|---------------|-------|
| `remainder_k` | remainder k = B mod M | bridge residue, gap d in near-power examples | The residue of the block base B modulo the purely periodic modulus M in B = qM + k. | all coprime moduli |
| `quotient_q` | quotient q = (B-k)/M | bridge factor | The quotient in the canonical decomposition B = qM + k. It supplies the missing factor in the exact geometric series. | all coprime moduli |
| `skeleton` | raw coefficients qk^j | skeleton, raw powers in the q=1 bridge case | The uncarried block coefficients in the exact identity 1/M = Σ qk^j / B^(j+1). | all coprime moduli |
| `carry_layer` | carry-propagated block normalization | carry layer | The deterministic carry process that converts raw coefficients into admissible base-B blocks. | all coprime moduli |
| `body_term` | body term W = (B^L - k^L)/M | orbit weave | The finite algebraic body term in the decomposition R = W + F. | all coprime moduli |
| `correction_term` | correction term F = (k^L - 1)/M | closure flux, cyclic flux | The finite correction term completing the reptend decomposition R = W + F. | all coprime moduli |
| `good_mode` | small-residue block coordinate | good coordinates, bridge mode | A block width m for which B = base^m exceeds M and the residue k = B mod M is small enough to make early coefficients easy to read. | all coprime moduli |
| `qr_generator` | generator of the quadratic-residue subgroup | QR-generator | An element of order (p-1)/2 in (Z/pZ)*, equivalently a generator of the subgroup of quadratic residues. | odd primes |
| `remainder_orbit` | remainder orbit under multiplication by the base | circle walk | The long-division remainder sequence r_{n+1} = Br_n mod N, interpreted as a walk on the unit group. | all coprime moduli |
<!-- VOCABULARY_TABLE_END -->

Machine-readable backing lives in [vocabulary.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/vocabulary.json).
