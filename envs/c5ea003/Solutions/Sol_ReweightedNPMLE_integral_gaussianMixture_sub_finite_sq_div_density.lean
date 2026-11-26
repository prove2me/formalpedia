-- Prove2me | solution 1 for ReweightedNPMLE.integral_gaussianMixture_sub_finite_sq_div_density
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:23.647856+00:00
-- url     : https://prove2.me/submissions/69ec89a9-d75d-4b41-a985-6759d0253d37

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_kernel_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_sq_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_integral_finiteGaussianMixture_sq_div_density
import Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_mul_kernel_div_density
import Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_sq_div_density

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

/-- Weighted square error of a finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_sq_div_density_integrable
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    Integrable (fun x ↦
      (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x) := by
  apply (integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦
      (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
        (c i * c j)).congr
  exact Filter.Eventually.of_forall fun x ↦
    (finiteGaussianMixture_sq_div_density_eq_sum_overlap c θ x).symm









end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasureHellinger.
section
/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE



theorem integral_gaussianMixture_mul_finiteGaussianMixture_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
        gaussianMixture μ θ x * finiteGaussianMixture w z x /
          gaussianDensity d x =
      ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ := by
  have hcomponent (i : ι) := gaussianMixture_mul_kernel_div_density_integrable
    μ θ hθmeas hS hθS (z i) (hzS i)
  calc
    (∫ x : Point d,
        gaussianMixture μ θ x * finiteGaussianMixture w z x /
          gaussianDensity d x) =
        ∫ x : Point d, ∑ i, w i *
          (gaussianMixture μ θ x * gaussianKernel d x (z i) /
            gaussianDensity d x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold finiteGaussianMixture
        change gaussianMixture μ θ x * (∑ i, w i * gaussianKernel d x (z i)) /
            gaussianDensity d x =
          ∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
            gaussianDensity d x)
        rw [Finset.mul_sum]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ∑ i, ∫ x : Point d, w i *
        (gaussianMixture μ θ x * gaussianKernel d x (z i) /
          gaussianDensity d x) := by
      rw [integral_finsetSum Finset.univ]
      intro i _
      exact (hcomponent i).const_mul (w i)
    _ = ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul,
        integral_gaussianMixture_mul_kernel_div_density
          μ θ hθmeas hS hθS (z i) (hzS i)]



































end ReweightedNPMLE
end

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x =
      (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) := by
  have hp := gaussianMixture_sq_div_density_integrable μ θ hθmeas hS hθS
  have hpq := gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hq := finiteGaussianMixture_sq_div_density_integrable w z
  have hpq2 : Integrable (fun x : Point d ↦
      2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
        gaussianDensity d x)) := hpq.const_mul 2
  calc
    _ = ∫ x : Point d,
        (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = (∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
            2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
              gaussianDensity d x)) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      exact integral_add (hp.sub hpq2) hq
    _ = ((∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) -
        ∫ x : Point d,
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x)) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      rw [integral_sub hp hpq2]
    _ = (∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) -
        2 * (∫ x : Point d,
          gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_gaussianMixture_sq_div_density μ θ hθmeas hS hθS,
        integral_gaussianMixture_mul_finiteGaussianMixture_div_density
          μ θ hθmeas w z hS hθS hzS,
        integral_finiteGaussianMixture_sq_div_density]
