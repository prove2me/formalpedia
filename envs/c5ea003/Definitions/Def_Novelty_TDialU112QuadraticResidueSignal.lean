-- Prove2me | Definitions.Def_Novelty_TDialU112QuadraticResidueSignal
-- name    : Novelty_TDialU112QuadraticResidueSignal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:41.134081+00:00
-- url     : https://prove2.me/theorems/f9e4cd42-203b-4c17-82ac-84316dfb77a7
-- title:
--   Aether Catalog definitions — Novelty_TDialU112QuadraticResidueSignal
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TDialU112QuadraticResidueSignal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TDialU112QuadraticResidueSignal.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.TDialU112QuadraticResidueSignal

/-! ## 1. The residue count at a single small prime -/

/-- The nonzero quadratic residues mod `m`. -/
def qrSet (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  univ.filter (fun a : ZMod m => a ≠ 0 ∧ IsSquare a)

/-- The quadratic non-residues mod `m`. -/
def nqrSet (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  univ.filter (fun a : ZMod m => a ≠ 0 ∧ ¬ IsSquare a)






/-! ## 2. CRT independence of the residue bits -/

/-- Reduction of `x mod mn` to `x mod m`. -/
def redFst (m n : ℕ) : ZMod (m * n) →+* ZMod m := ZMod.castHom ⟨n, rfl⟩ (ZMod m)

/-- Reduction of `x mod mn` to `x mod n`. -/
def redSnd (m n : ℕ) : ZMod (m * n) →+* ZMod n := ZMod.castHom ⟨m, mul_comm m n⟩ (ZMod n)




/-! ## 3. The two-prime dial and its exact law -/

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

/-- Residues mod `pq` that are quadratic residues at both primes. -/
def patternSS : Finset (ZMod (p * q)) :=
  univ.filter (fun x => redFst p q x ∈ qrSet p ∧ redSnd p q x ∈ qrSet q)

/-- Residue at `p`, non-residue at `q`. -/
def patternSN : Finset (ZMod (p * q)) :=
  univ.filter (fun x => redFst p q x ∈ qrSet p ∧ redSnd p q x ∈ nqrSet q)

/-- Non-residue at `p`, residue at `q`. -/
def patternNS : Finset (ZMod (p * q)) :=
  univ.filter (fun x => redFst p q x ∈ nqrSet p ∧ redSnd p q x ∈ qrSet q)

/-- Non-residue at both primes. -/
def patternNN : Finset (ZMod (p * q)) :=
  univ.filter (fun x => redFst p q x ∈ nqrSet p ∧ redSnd p q x ∈ nqrSet q)

/-- The two-prime QR dial: how many of the two small primes see `x` as a quadratic residue. -/
def qrDial (x : ZMod (p * q)) : ℕ :=
  (if redFst p q x ∈ qrSet p then 1 else 0) + (if redSnd p q x ∈ qrSet q then 1 else 0)

variable {p q}





/-! ### The dial level sets -/







/-- The dial level `1` set. -/
def dialOne : Finset (ZMod (p * q)) := patternSN p q ∪ patternNS p q



/-- The unit part of `ZMod (pq)`: residues invertible at both primes. -/
def unitPart : Finset (ZMod (p * q)) :=
  patternSS p q ∪ (patternSN p q ∪ (patternNS p q ∪ patternNN p q))




end Catalog.Novelty.TDialU112QuadraticResidueSignal


