-- Prove2me | solution 1 for ReweightedNPMLE.log_one_add_ge_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:01:51.670571+00:00
-- url     : https://prove2.me/submissions/ee7bedb0-9087-41a1-a3a8-c59389bc0a9e

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set
/-- The lower logarithm bound used in the Gamma change-of-variables
argument.  The paper only needs the smaller radius `1/8`. -/
theorem solution {u : ℝ} (hu : |u| ≤ 1 / 8) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun x ↦ Real.log (1 + x) - x + x ^ 2
  have hfderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt f (x * (1 + 2 * x) / (1 + x)) x := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hne
    convert (hlog.sub (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [Pi.add_apply, Pi.one_apply, id_eq] <;> field_simp <;> ring
  by_cases hu0 : 0 ≤ u
  · have hmono : MonotoneOn f (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hxupper : x ≤ 1 / 8 := hx.2.le.trans ((le_abs_self u).trans hu)
        exact div_nonneg (mul_nonneg hx.1.le (by linarith [hx.1])) (by linarith [hx.1])
    have h := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
    dsimp [f] at h
    norm_num at h
    linarith
  · have hule : u ≤ 0 := le_of_not_ge hu0
    have hanti : AntitoneOn f (Set.Icc u 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
      · intro x hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by
          have hulower : -(1 / 8 : ℝ) ≤ u := by
            have := neg_le_of_abs_le hu
            norm_num at this ⊢
            exact this
          rw [interior_Icc] at hx
          linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        have hxden : 0 < 1 + x := by linarith [hx.1]
        have hlin : 0 ≤ 1 + 2 * x := by linarith [hx.1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hx.2.le hlin) hxden.le
    have h := hanti (left_mem_Icc.mpr hule) (right_mem_Icc.mpr hule) hule
    dsimp [f] at h
    norm_num at h
    linarith
