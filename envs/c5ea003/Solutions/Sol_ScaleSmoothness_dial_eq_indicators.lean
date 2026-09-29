-- Prove2me | solution 1 for ScaleSmoothness.dial_eq_indicators
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:46:44.549559+00:00
-- url     : https://prove2.me/submissions/c31d2b08-5d03-44db-8457-c8368a1408f3

-- Sol generated from NumberTheory/QuadraticDialIndependence.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
import Theorems.Thm_ScaleSmoothness_dial_eq_two_iff
import Theorems.Thm_ScaleSmoothness_dial_eq_zero_of_not_isSquare
import Theorems.Thm_ScaleSmoothness_dial_le_two
import Theorems.Thm_ScaleSmoothness_dial_zero

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







/-! ### Joint uniformity of the dial vector -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ### Extremes of the structure correction -/





open ScaleSmoothness in
theorem solution(hp : p ≠ 2) (N : ZMod p) :
    dial p N = 2 * (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0) := by
  by_cases h0 : N = 0
  · subst h0
    rw [dial_zero p hp]
    norm_num
  · have hle := dial_le_two p hp N
    by_cases h2 : dial p N = 2
    · rw [h2]; simp [h0]
    · have : dial p N = 0 := by
        rcases Nat.lt_or_ge (dial p N) 2 with h | h
        · interval_cases hh : dial p N
          · rfl
          · exfalso
            have hsq : IsSquare N := by
              by_contra hns
              rw [dial_eq_zero_of_not_isSquare p hns] at hh
              exact absurd hh (by norm_num)
            rw [(dial_eq_two_iff p hp h0).2 hsq] at hh
            exact absurd hh (by norm_num)
        · omega
      rw [this]; simp [h0]
