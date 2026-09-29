-- Prove2me | solution 1 for ProfileForm.uniformResidual_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:06:30.278588+00:00
-- url     : https://prove2.me/submissions/8a685a64-33f7-48f5-9ef0-45ccb6d0b588

-- Sol generated from NumberTheory/ProfileFormUniformMixturePeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak
import Theorems.Thm_ProfileForm_dickmanMixtureBaseline_pos

/-!
# Profile form VII: even the Dickman surrogate humps — outside the window

Second Stage-4 (Critic) result of this cycle, sharper than the two-atom
counterexample of `ProfileFormMixturePeak`.

The mixture-Dickman baseline actually used in the analysis is the *uniform*
scale mixture `M(x) = (1 - e^{-x})/x`.  On the measured window `x ∈ [0,1]` the
residual `T/M` of a power law against it is decreasing, which is why the
observed hump looks like new physics.  But the crossing of the two competing
log-slopes `b/(1+x)` (from the profile) and `1/x - 1/(e^x - 1)` (from the
mixture) happens near `x ≈ 10`, and there the residual really does peak.

We prove this for the measured exponent `b = 11/10`:

`uniformResidual 3 < uniformResidual 10` and `uniformResidual 100 <
uniformResidual 10`,

hence `uniformResidual` attains an interior maximum on `[3, 100]` and is neither
monotone nor antitone there (`uniformResidual_peak`).

Consequence (`peak_is_window_dependent`): *peakedness of the residual is a
window-relative statement*, not an intrinsic property distinguishing the
baseline.  Combined with `ProfileFormResidualPeak.peak_forces_nonPowerLaw_baseline`,
the defensible reading of the experiment is: the measured hump at `x ≈ 0.59`
locates a feature *inside* the analysed window, and its interpretation must be
tied to that window.

The numerical work is done with the rational-exponent trick
`rpow_eleven_tenths_le` / `le_rpow_eleven_tenths`, which converts a bound on
`a ^ (11/10)` into an exact comparison of integer powers.
-/

open ProfileForm

open Set

/-! ## Interior maxima on a general window -/




/-! ## Rational exponents as integer power comparisons -/



/-! ## The residual against the uniform (Dickman surrogate) mixture -/












open ProfileForm in
theorem solution: ContinuousOn uniformResidual (Icc (3:ℝ) 100) := by
  have hfun : powerProfile 1 (11/10) = fun x : ℝ => (1 + x) ^ (-(11/10) : ℝ) := by
    funext x; simp [powerProfile]
  apply ContinuousOn.div
  · rw [hfun]
    intro x hx
    have hpos : (0:ℝ) < 1 + x := by have := hx.1; linarith
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hpos))).continuousWithinAt.comp
      (by fun_prop : ContinuousWithinAt (fun x : ℝ => 1 + x) (Icc (3:ℝ) 100) x)
      (fun y _ => Set.mem_univ _)
  · intro x hx
    have hx0 : x ≠ 0 := by have := hx.1; intro h; rw [h] at this; linarith
    unfold dickmanMixtureBaseline
    have hnum : ContinuousWithinAt (fun x : ℝ => 1 - Real.exp (-x)) (Icc (3:ℝ) 100) x := by
      fun_prop
    exact hnum.div continuousWithinAt_id hx0
  · intro x hx
    have hx0 : (0:ℝ) < x := by have := hx.1; linarith
    exact ne_of_gt (dickmanMixtureBaseline_pos hx0)
