-- Prove2me | solution 1 for Catalog.Novelty.TDialU112QuadraticResidueSignal.two_mul_card_qrSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:23:28.742707+00:00
-- url     : https://prove2.me/submissions/0672363e-632e-4a37-8f78-1bfcd522054d

-- Sol generated from Novelty/TDialU112QuadraticResidueSignal.lean
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



lemma card_qrSet_add_card_nqrSet (p : ℕ) [Fact p.Prime] :
    (qrSet p).card + (nqrSet p).card = p - 1 := by
  have hS : Finset.filter (fun a : ZMod p => IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = qrSet p := Finset.filter_filter _ _ _
  have hN : Finset.filter (fun a : ZMod p => ¬ IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = nqrSet p := Finset.filter_filter _ _ _
  rw [← hS, ← hN, Finset.card_filter_add_card_filter_not]
  have hE : (univ.filter (fun a : ZMod p => a ≠ 0)) = univ.erase (0 : ZMod p) := by
    ext a; simp [Finset.mem_erase]
  rw [hE, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]





/-! ## 2. CRT independence of the residue bits -/






/-! ## 3. The two-prime dial and its exact law -/

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]






variable {p q}





/-! ### The dial level sets -/















open Catalog.Novelty.TDialU112QuadraticResidueSignal in
theorem solution(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * (qrSet p).card = p - 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have h0 : ∑ a : ZMod p, quadraticChar (ZMod p) a = 0 := quadraticChar_sum_zero hchar
  have hne : ∑ a ∈ univ.filter (fun a : ZMod p => a ≠ 0), quadraticChar (ZMod p) a = 0 := by
    rw [← h0]
    refine Finset.sum_subset (f := fun a : ZMod p => quadraticChar (ZMod p) a)
      (Finset.filter_subset (fun a : ZMod p => a ≠ 0) univ) ?_
    intro x _ hx
    simp only [mem_filter, mem_univ, true_and, not_not] at hx
    simp [hx]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (univ.filter (fun a : ZMod p => a ≠ 0)) (fun a : ZMod p => IsSquare a)
    (quadraticChar (ZMod p))
  have hS : Finset.filter (fun a : ZMod p => IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = qrSet p := Finset.filter_filter _ _ _
  have hN : Finset.filter (fun a : ZMod p => ¬ IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = nqrSet p := Finset.filter_filter _ _ _
  have hsum1 : ∑ a ∈ qrSet p, quadraticChar (ZMod p) a = ((qrSet p).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun a ha => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [qrSet, mem_filter] at ha
    exact (quadraticChar_one_iff_isSquare ha.2.1).mpr ha.2.2
  have hsum2 : ∑ a ∈ nqrSet p, quadraticChar (ZMod p) a = -((nqrSet p).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun a ha => ?_), Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    simp only [nqrSet, mem_filter] at ha
    exact quadraticChar_neg_one_iff_not_isSquare.mpr ha.2.2
  rw [hS, hN, hsum1, hsum2, hne] at hsplit
  have hcard := card_qrSet_add_card_nqrSet p
  omega
