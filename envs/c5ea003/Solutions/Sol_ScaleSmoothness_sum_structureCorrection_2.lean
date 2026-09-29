-- Prove2me | solution 2 for ScaleSmoothness.sum_structureCorrection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:29:29.896838+00:00
-- url     : https://prove2.me/submissions/a3dcc578-561d-4322-9122-32510c3ffc22

/-
# `ScaleSmoothness.sum_structureCorrection`
Target `cc0dbcc2` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

The sum over the pi-type of a coordinatewise product factors into a product of sums, leaving
one fact per coordinate: `∑ N : ZMod p, localFactor p N = p`. That is a fibre count — each `x`
lies in exactly one fibre `N = x²`, so `∑ N dial p N = #(ZMod p) = p` — followed by
`(p·p - p)/(p - 1) = p`, valid since `p` is prime so `(p:ℚ) - 1 > 0`.

Verified exactly over ℚ before drafting: the per-coordinate identity for every prime up to 31,
and the full claim brute-forced over the whole pi-type for [3], [3,5], [3,5,7], [5,7], [2,3,5],
[3,3], [11,13], [3,5,7,11].

EVERY LEMMA BELOW WAS PROBED, NOT GUESSED. Observed facts driving this proof:
  * `Finset.prod_univ_sum` runs  ∏ᵢ ∑ⱼ  →  ∑ over `Fintype.piFinset`, i.e. the OPPOSITE
    orientation to the goal, so it is applied to the product side and then reconciled with
    `Fintype.piFinset_univ : (Fintype.piFinset fun a => univ) = univ`.
  * `Finset.card_eq_sum_card_fiberwise` closes the fibre count exactly as written below.
  * `localFactor p N = ((p:ℚ) - dial p N)/((p:ℚ) - 1)` holds by `rfl`.
  * traced goal after `← Finset.sum_div` is  `(∑ i, (↑p - ↑(dial p i))) / (↑p - 1) = ↑p`.

`hodd` is unused: the identity holds at `p = 2` too (checked on the family [2,3,5]). It is in
the binder list only because the source preamble says `include hodd`.
-/
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Finset ScaleSmoothness

/-- Per coordinate: the local factor sums to the modulus. -/
theorem coord_sum (p : ℕ) [NeZero p] [Fact (Nat.Prime p)] :
    (∑ N : ZMod p, localFactor p N) = (p : ℚ) := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  -- fibre count: every x lands in exactly one fibre N = x²
  have hd : (∑ N : ZMod p, dial p N) = Fintype.card (ZMod p) := by
    simp only [dial]
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod p => x ^ 2)
          (t := (Finset.univ : Finset (ZMod p))) (fun x _ => Finset.mem_univ _)]
    simp
  -- p prime, so (p : ℚ) - 1 is strictly positive and in particular nonzero
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hq2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp2
  have hpos : (0:ℚ) < (p:ℚ) - 1 := by linarith
  have hp1 : (p:ℚ) - 1 ≠ 0 := hpos.ne'
  simp only [localFactor]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard,
      ← Nat.cast_sum, hd, hcard, nsmul_eq_mul, div_eq_iff hp1]
  ring

/-- **The target, verbatim.** -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2) :
    ∑ N : (∀ i, ZMod (a i)), structureCorrection a N = ∏ i, (a i : ℚ) := by
  have step : (∑ N : (∀ i, ZMod (a i)), structureCorrection a N)
      = ∏ i, (∑ n : ZMod (a i), localFactor (a i) n) := by
    simp only [structureCorrection]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [step]
  exact Finset.prod_congr rfl (fun i _ => coord_sum (a i))
