-- Prove2me | solution 1 for ReweightedNPMLE.neg_sub_log_one_sub_ge_sq_div_two
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:35.228418+00:00
-- url     : https://prove2.me/submissions/6617eac5-9d5f-4e01-909c-6716e2b6cfcd

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Scalar inequalities for Gamma concentration

These are the two elementary logarithmic estimates used in Lemma 9.1 of the manuscript.
-/

open Set
theorem solution {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    -t - Real.log (1 - t) ≥ t ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x ↦ -x - Real.log (1 - x) - x ^ 2 / 2
  have hfderiv : ∀ x : ℝ, x < 1 → HasDerivAt f (x ^ 2 / (1 - x)) x := by
    intro x hx
    have hne : 1 - x ≠ 0 := by linarith
    have hinner := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hlog := hinner.log hne
    convert (hasDerivAt_id x).neg.sub hlog |>.sub
      (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      simp only [Pi.sub_apply, Pi.one_apply, id_eq] <;>
      field_simp <;> ring
  have hmono : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hfderiv x (hx.2.trans_lt ht₁)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfderiv x (by
        rw [interior_Icc] at hx
        exact hx.2.trans ht₁)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hfderiv x (by
        rw [interior_Icc] at hx
        exact hx.2.trans ht₁)).deriv]
      rw [interior_Icc] at hx
      exact div_nonneg (sq_nonneg x) (by linarith [hx.2, ht₁])
  have h := hmono (left_mem_Icc.mpr ht₀) (right_mem_Icc.mpr ht₀) ht₀
  dsimp [f] at h
  norm_num at h
  linarith
