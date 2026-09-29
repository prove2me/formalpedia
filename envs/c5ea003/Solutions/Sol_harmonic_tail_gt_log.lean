-- Prove2me | solution 1 for harmonic_tail_gt_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:32:11.276857+00:00
-- url     : https://prove2.me/submissions/6119be30-4327-43f4-8ac4-418f4c4cacc5

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open scoped BigOperators
open Finset


-- per-term strict bound: log((j+2)/(j+1)) < 1/(j+1)
theorem hlg_term_gt (j : ℕ) :
    Real.log (((j:ℝ)+2) / (j+1)) < (1 : ℝ) / (j + 1) := by
  -- log(1 + 1/(j+1)) < 1/(j+1), via log_lt_sub_one_of_pos applied to x = (j+2)/(j+1) > 1
  have hjpos : (0:ℝ) < (j:ℝ)+1 := by positivity
  set x : ℝ := ((j:ℝ)+2)/((j:ℝ)+1) with hx_def
  have hxpos : 0 < x := by rw [hx_def]; positivity
  have hxne : x ≠ 1 := by
    rw [hx_def]
    have : (1:ℝ) < ((j:ℝ)+2)/((j:ℝ)+1) := by
      rw [lt_div_iff₀ hjpos]; linarith
    linarith
  have hkey := Real.log_lt_sub_one_of_pos hxpos hxne
  -- x - 1 = 1/(j+1)
  have hx1 : x - 1 = 1 / ((j:ℝ)+1) := by rw [hx_def]; field_simp; ring
  rw [hx1] at hkey
  exact hkey

/-- **Harmonic-tail lower bound (strict).** `∑_{j∈[a,b)} 1/(j+1) > log((b+1)/(a+1))` for `a < b`.
This is the lower companion of `harmonic_tail_lt_log`; per-term `log((j+2)/(j+1)) < 1/(j+1)`
(i.e. `log(1+x) < x`), telescoped. -/
theorem solution (a b : ℕ) (hab : a < b) :
    Real.log (((b:ℝ)+1) / (a+1)) < (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) := by
  have htel : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+2) / (j+1))) = Real.log (((b:ℝ)+1)/(a+1)) := by
    have hcongr : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+2) / (j+1)))
        = ∑ j ∈ Finset.Ico a b, (Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hcongr, Finset.sum_Ico_eq_sum_range]
    have hstep : (∑ i ∈ Finset.range (b - a), (Real.log (((a+i:ℕ):ℝ)+2) - Real.log (((a+i:ℕ):ℝ)+1)))
        = ∑ i ∈ Finset.range (b - a),
            ((fun k => Real.log (((a+k:ℕ):ℝ)+1)) (i+1) - (fun k => Real.log (((a+k:ℕ):ℝ)+1)) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only []
      have : ((a + (i+1) : ℕ) : ℝ) + 1 = ((a+i:ℕ):ℝ) + 2 := by push_cast; ring
      rw [this]
    rw [hstep, Finset.sum_range_sub (fun k => Real.log (((a+k:ℕ):ℝ)+1)) (b-a)]
    have hba : a + (b - a) = b := by omega
    rw [show (a + (b-a) : ℕ) = b from hba, Nat.add_zero]
    rw [← Real.log_div (by positivity) (by positivity)]
  rw [← htel]
  apply Finset.sum_lt_sum_of_nonempty
  · rw [Finset.nonempty_Ico]; exact hab
  · intro j _
    exact hlg_term_gt j
