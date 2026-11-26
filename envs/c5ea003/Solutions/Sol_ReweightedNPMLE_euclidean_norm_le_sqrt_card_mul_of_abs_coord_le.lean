-- Prove2me | solution 1 for ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:06:02.650997+00:00
-- url     : https://prove2.me/submissions/1e3e7603-13d1-405a-a96f-360f21a9a63d

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- If every coordinate is at most `t` in absolute value, the Euclidean norm
is at most `sqrt d * t`. -/
theorem solution
    {d : ℕ} (z : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ i, |z i| ≤ t) :
    ‖WithLp.toLp 2 z‖ ≤ Real.sqrt d * t := by
  have hsum : ∑ i : Fin d, (z i) ^ 2 ≤ ∑ _i : Fin d, t ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := (sq_le_sq₀ (abs_nonneg (z i)) ht).2 (hz i)
    simpa only [sq_abs] using hi
  have hnormsq : ‖WithLp.toLp 2 z‖ ^ 2 ≤ (d : ℝ) * t ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using hsum
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtd : (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  have hrhs : 0 ≤ Real.sqrt d * t := mul_nonneg hsqrt ht
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).1
  rw [mul_pow, hsqrtd]
  exact hnormsq
