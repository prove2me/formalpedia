-- Prove2me | solution 1 for ReweightedNPMLE.abs_finiteGaussianMixture_weight_relative_error_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:53:12.810865+00:00
-- url     : https://prove2.me/submissions/26689aef-6710-4606-a2c2-d396b277ca38

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_le

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureNet.
section
/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE







/-- Exact factorization of a finite Gaussian mixture into the centered
Gaussian density and its exponential-score normalizer. -/
theorem finiteGaussianMixture_eq_density_mul_score_sum
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    finiteGaussianMixture w θ x = gaussianDensity d x *
      ∑ i, w i * Real.exp (gaussianScore x (θ i)) := by
  unfold finiteGaussianMixture
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianKernel_eq_density_mul_exp_score]
  ring





















end ReweightedNPMLE
end

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Rounding the weights of a finite mixture produces a relative density
error controlled by the `ℓ¹` weight error and the local Gaussian score
envelope. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) :
    |finiteGaussianMixture v θ x / finiteGaussianMixture w θ x - 1| ≤
      Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| := by
  let B := T * S + S ^ 2 / 2
  let A := ∑ i, w i * Real.exp (gaussianScore x (θ i))
  let C := ∑ i, v i * Real.exp (gaussianScore x (θ i))
  have hscore (i : ι) : |gaussianScore x (θ i)| ≤ B := by
    simpa only [B] using abs_gaussianScore_le hT hS hx (hθ i)
  have hA : Real.exp (-B) ≤ A := by
    calc
      Real.exp (-B) = (∑ i, w i) * Real.exp (-B) := by rw [hwsum, one_mul]
      _ = ∑ i, w i * Real.exp (-B) := by rw [Finset.sum_mul]
      _ ≤ ∑ i, w i * Real.exp (gaussianScore x (θ i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_of_abs_le (hscore i))) (hw i)
      _ = A := rfl
  have hApos : 0 < A := (Real.exp_pos (-B)).trans_le hA
  have hCA : |C - A| ≤ Real.exp B * ∑ i, |v i - w i| := by
    calc
      |C - A| = |∑ i, (v i - w i) * Real.exp (gaussianScore x (θ i))| := by
        dsimp only [C, A]
        rw [← Finset.sum_sub_distrib]
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, |(v i - w i) * Real.exp (gaussianScore x (θ i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |v i - w i| * Real.exp (gaussianScore x (θ i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ ∑ i, |v i - w i| * Real.exp B := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ((le_abs_self _).trans (hscore i)))
          (abs_nonneg _)
      _ = Real.exp B * ∑ i, |v i - w i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hratio :
      finiteGaussianMixture v θ x / finiteGaussianMixture w θ x = C / A := by
    rw [finiteGaussianMixture_eq_density_mul_score_sum,
      finiteGaussianMixture_eq_density_mul_score_sum]
    exact mul_div_mul_left C A (gaussianDensity_pos d x).ne'
  rw [hratio, div_sub_one hApos.ne', abs_div, abs_of_pos hApos]
  calc
    |C - A| / A ≤
        (Real.exp B * ∑ i, |v i - w i|) / Real.exp (-B) := by
      exact div_le_div₀ (by positivity) hCA (Real.exp_pos _) hA
    _ = Real.exp (2 * B) * ∑ i, |v i - w i| := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        (Real.exp B * ∑ i, |v i - w i|) * Real.exp (- -B) =
            (Real.exp B * Real.exp (- -B)) * ∑ i, |v i - w i| := by ring
        _ = Real.exp (B + - -B) * ∑ i, |v i - w i| := by rw [← Real.exp_add]
        _ = Real.exp (2 * B) * ∑ i, |v i - w i| := by congr 2 <;> ring
    _ = Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| := rfl
