-- Prove2me | solution 1 for ScaleSmoothness.two_mul_card_dial_zero_add_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:53:26.216661+00:00
-- url     : https://prove2.me/submissions/360dc759-19dc-4344-b854-83eae78b6146

-- Sol generated from NumberTheory/QuadraticDialIndependence.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
import Theorems.Thm_ScaleSmoothness_dial_eq_indicators
import Theorems.Thm_ScaleSmoothness_dial_zero
import Theorems.Thm_ScaleSmoothness_sum_dial

/-!
# The dial vector of `x² − N` is exactly uniform: an independence theorem

`Catalog.NumberTheory.QRDialLocalStatistics` computed the moments of the QR dial
`dial p N = #{x | x² = N}` and
`Catalog.NumberTheory.ScaleSmoothnessDispersion` assembled them into the global
structure correction.  This file proves the *distributional* statement that
underlies the experimental design of round-73 #4 (exp 562): the vector of dials
`(dial p N)_{p ≤ B}` is **exactly uniform** on `{0,2}^k` as `N` ranges over the
residue data — the quadratic-residue pattern of `N` carries no bias whatsoever,
prime by prime *and jointly*.

## Main results

* `dial_eq_one_add_quadraticChar` — the bridge to Mathlib's quadratic character:
  `dial p N = 1 + χ_p(N)` as integers, valid for **all** `N`, including `N = 0`.
* `sum_quadraticChar_eq_zero` — an immediate consequence of the exact first
  moment `∑_N dial p N = p`: the quadratic character sums to zero.
* `two_mul_card_dial_two_add_one`, `two_mul_card_dial_zero_add_one` — exactly
  `(p−1)/2` residues are hit twice and `(p−1)/2` are missed.
* `card_dial_pattern` — **joint uniformity / independence**: for every prescribed
  pattern `d : ι → {0,2}` the number of residue data realising it is exactly
  `∏ (a i − 1) / 2^k`, independent of the pattern.
* `structureCorrection_max_value`, `card_structureCorrection_max` — the extreme
  values of the structure correction and the exact number of residue data
  attaining them.  Only a `2^{-k}` fraction of `N` sits at either extreme, which
  is why the observed clustering is `O(1)` and not exponential.
-/

open ScaleSmoothness

open Finset


variable (p : ℕ) [Fact p.Prime]




/-- Exactly `(p−1)/2` residues are hit twice by `x² − N`. -/
theorem two_mul_card_dial_two_add_one (hp : p ≠ 2) :
    2 * #{N : ZMod p | dial p N = 2} + 1 = p := by
  have h := sum_dial p
  have hsplit : ∑ N : ZMod p, dial p N =
      2 * #{N : ZMod p | dial p N = 2} + #{N : ZMod p | N = 0} := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun N _ => dial_eq_indicators p hp N
  have hzero : #{N : ZMod p | N = 0} = 1 := by
    rw [Finset.filter_eq' univ (0 : ZMod p)]
    simp
  rw [hsplit, hzero] at h
  exact h



/-! ### Joint uniformity of the dial vector -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ### Extremes of the structure correction -/





open ScaleSmoothness in
theorem solution(hp : p ≠ 2) :
    2 * #{N : ZMod p | dial p N = 0} + 1 = p := by
  have hpart : ∀ N : ZMod p,
      (if dial p N = 0 then 1 else 0) + (if dial p N = 2 then 1 else 0)
        + (if N = 0 then 1 else 0) = 1 := by
    intro N
    by_cases h0 : N = 0
    · subst h0
      rw [dial_zero p hp]; norm_num
    · have hind := dial_eq_indicators p hp N
      by_cases h2 : dial p N = 2
      · simp [h2, h0]
      · have h0' : dial p N = 0 := by
          rw [if_neg h2, if_neg h0] at hind; omega
        simp [h0', h0]
  have hsum : ∑ N : ZMod p, ((if dial p N = 0 then 1 else 0)
      + (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0)) = p := by
    rw [Finset.sum_congr rfl fun N _ => hpart N]
    simp [ZMod.card]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter,
    ← Finset.card_filter] at hsum
  have hzero : #{N : ZMod p | N = 0} = 1 := by
    rw [Finset.filter_eq' univ (0 : ZMod p)]; simp
  have h2 := two_mul_card_dial_two_add_one p hp
  rw [hzero] at hsum
  omega
