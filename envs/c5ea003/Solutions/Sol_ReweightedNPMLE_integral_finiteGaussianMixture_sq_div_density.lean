-- Prove2me | solution 1 for ReweightedNPMLE.integral_finiteGaussianMixture_sq_div_density
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:55.705542+00:00
-- url     : https://prove2.me/submissions/d0ee6a49-f5a5-472f-9cd7-641bf6db0a47

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density
import Theorems.Thm_ReweightedNPMLE_integral_gaussianKernel_product_div_density

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

















































/-- The Gaussian overlap integrand is integrable. -/
theorem gaussianKernel_product_div_density_integrable
    {d : ℕ} (θ η : Point d) :
    Integrable (fun x ↦
      gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x) := by
  apply ((gaussianDensity_integrable d).comp_sub_right (θ + η)).const_mul
    (Real.exp (inner ℝ θ η)) |>.congr
  exact Filter.Eventually.of_forall fun x ↦
    (gaussianKernel_product_div_density x θ η).symm

/-- Expanding the square of a finite signed mixture gives a double sum of
Gaussian overlap terms. -/
theorem finiteGaussianMixture_sq_div_density_eq_sum_overlap
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x =
      ∑ i, ∑ j, c i * c j *
        (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
          gaussianDensity d x) := by
  unfold finiteGaussianMixture
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring











end ReweightedNPMLE
end

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Exact finite quadratic-form identity for a signed Gaussian mixture.  It
is the finite-support version of the manuscript's global `Q_m` identity. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x =
      ∑ i, ∑ j, c i * c j * Real.exp (inner ℝ (θ i) (θ j)) := by
  calc
    (∫ x, (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x) =
        ∫ x, ∑ i, ∑ j, c i * c j *
          (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
            gaussianDensity d x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        finiteGaussianMixture_sq_div_density_eq_sum_overlap c θ x
    _ = ∑ i, ∑ j, ∫ x, c i * c j *
          (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
            gaussianDensity d x) := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ]
        intro j hj
        exact (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
          (c i * c j)
      · intro i hi
        exact integrable_finsetSum Finset.univ fun j hj ↦
          (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
            (c i * c j)
    _ = ∑ i, ∑ j, c i * c j * Real.exp (inner ℝ (θ i) (θ j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_gaussianKernel_product_div_density]
