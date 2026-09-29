-- Prove2me | Theorems.Thm_Catalog_Novelty_TDialU112QuadraticResidueSignal_two_mul_card_qrSet
-- name    : Catalog.Novelty.TDialU112QuadraticResidueSignal.two_mul_card_qrSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:17:00.975572+00:00
-- url     : https://prove2.me/theorems/7be5b9ac-8dd7-4700-9c6d-215c03dc8f00
-- title:
--   Exactly half of the nonzero residues are squares.
-- statement:
--   **Exactly half of the nonzero residues are squares.**  For an odd prime `p`,
--   `2 · |QR(p)| = p − 1`.  The proof runs through the vanishing of the quadratic character sum,
--   so it uses the multiplicative structure of `(ZMod p)ˣ`, not a counting bijection.
--
--   ```lean
--   theorem Catalog.Novelty.TDialU112QuadraticResidueSignal.two_mul_card_qrSet(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
--       2 * (qrSet p).card = p - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TDialU112QuadraticResidueSignal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TDialU112QuadraticResidueSignal.lean#L77

-- Thm stub generated from Novelty/TDialU112QuadraticResidueSignal.lean
import Mathlib
import Definitions.Def_Novelty_TDialU112QuadraticResidueSignal

/-!
# Where the residual dial signal comes from: exact equidistribution of the small-prime
# quadratic-residue pattern

## Research context (FACT round-70 #1, exp 545, `TDIAL-U112-CONTINUES-FADE`)

The U112 record (see `Novelty.TDialU112FadeReacceleration` for the statistical layer) reports a
pooled Spearman correlation of `0.462` between the dial statistic `T` and a downstream rate,
below the `0.55` band floor, and comments that "the residual `≈ 0.46` correlation is still far
above chance, so the small-prime QR pattern carries real per-`N` signal at bitlen 112".

Every earlier file in the thread treats the dial as an opaque real number attached to a run.
This file supplies the *arithmetic* layer that the sentence above presupposes: it proves, from
scratch, that the small-prime quadratic-residue pattern of a uniformly drawn integer is an
exactly equidistributed family of independent fair bits, so the dial is a genuinely
informative statistic of `N` at every bit length — a fact about `ℤ`, not about the experiment.

The point is a separation of concerns.  What fades with bit length is the *coupling* between
the dial and the downstream rate; the dial's own information content does **not** fade, and
this file computes it exactly.

## Main results

* `two_mul_card_qrSet` — for an odd prime `p`, exactly `(p−1)/2` nonzero residues are squares
  (stated as `2 · |QR(p)| = p − 1`, avoiding truncated division).  Proved from the vanishing
  of the quadratic-character sum.
* `two_mul_card_nqrSet` — the same count for the non-residues.
* `card_filter_crt` — **CRT independence in counting form**: for coprime moduli, the number of
  `x mod mn` whose two reductions satisfy prescribed conditions is the product of the two
  separate counts.  This is the precise sense in which the residue bits at distinct primes are
  independent.
* `card_pattern_SS`, `card_pattern_SN`, `card_pattern_NS`, `card_pattern_NN` — hence each of
  the four QR patterns at two distinct odd primes occurs exactly `(p−1)(q−1)/4` times.
* `qrDial_binomial` — the two-prime dial `T ∈ {0, 1, 2}` therefore has the exact
  `Binomial(2, 1/2)` law: `4·|T = 0| = 2·|T = 1| = 4·|T = 2| = (p−1)(q−1)`.
* `qrDial_takes_all_values` — all three levels are attained, so the dial is a nonconstant
  statistic on the unit part.
* `two_mul_dial_variance` — the exact second moment: `2 ∑ (T − 1)² = |units|`, i.e. the dial
  has variance exactly `1/2` — independent of the primes and hence of the bit length.

## Lab notes (exp 545, arithmetic layer)

```
p = 3,  q = 5 : |QR(3)| = 1, |QR(5)| = 2, pattern counts 2,2,2,2, dial law 2:4:2
p = 7,  q = 11: |QR(7)| = 3, |QR(11)| = 5, pattern counts 15 each, dial law 15:30:15
dial mean     : 1                       dial variance : 1/2   (all primes, all bitlens)
```
-/

open Finset
open scoped Classical

open Catalog.Novelty.TDialU112QuadraticResidueSignal

/-! ## 1. The residue count at a single small prime -/

theorem Catalog.Novelty.TDialU112QuadraticResidueSignal.two_mul_card_qrSet(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * (qrSet p).card = p - 1 := by sorry
