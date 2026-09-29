-- Prove2me | solution 1 for mme_entropy_le_cross_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:24:47.691994+00:00
-- url     : https://prove2.me/submissions/267fac9c-0962-4dd7-b1b9-60c1fa6c3fac

import Definitions.Def_mme_regional_entropy_rate_data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MME.RegionRate

/-- A subprobability reference measure bounds entropy by cross entropy when
it is positive wherever the probability distribution is positive. -/
theorem solution {W : Type*} [Fintype W]
    (p q : W → ℝ) (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hmass : ∑ w, p w = 1) (hqmass : ∑ w, q w ≤ 1)
    (hsupport : ∀ w, 0 < p w → 0 < q w) :
    entropy p ≤ -∑ w, p w * Real.log (q w) := by
  have hterm (w : W) : Real.negMulLog (p w) ≤
      -(p w * Real.log (q w)) + q w - p w := by
    by_cases hz : p w = 0
    · simpa [hz] using hq w
    · have hpos : 0 < p w := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hqpos := hsupport w hpos
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqpos hpos)
      rw [Real.log_div hqpos.ne' hz] at hlog
      have h := mul_le_mul_of_nonneg_left hlog (hp w)
      have hcancel : p w * (q w / p w) = q w := by field_simp
      simp only [mul_sub, hcancel, mul_one] at h
      rw [Real.negMulLog_def]
      linarith
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    hmass] at hsum
  unfold entropy
  linarith


#print axioms solution
