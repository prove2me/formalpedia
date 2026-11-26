-- Prove2me | solution 1 for ReweightedNPMLE.integral_abs_finiteGaussianMixture_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:15.946631+00:00
-- url     : https://prove2.me/submissions/137ab518-e4bd-4322-b63b-997196e596bb

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





































/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ

/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]

/-- Every finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_integrable {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    Integrable (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (gaussianKernel_integrable d (θ i)).const_mul (w i)

/-- The integral of a finite Gaussian mixture is the sum of its weights. -/
theorem integral_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    ∫ x, finiteGaussianMixture w θ x = ∑ i, w i := by
  unfold finiteGaussianMixture
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_gaussianKernel, mul_one]
  · intro i _
    exact (gaussianKernel_integrable d (θ i)).const_mul (w i)



















end ReweightedNPMLE
end

/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The `L¹` norm of a finite signed Gaussian mixture is bounded by the
`ℓ¹` norm of its coefficients. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, |finiteGaussianMixture c θ x| ≤ ∑ i, |c i| := by
  have hleft : Integrable (fun x ↦ |finiteGaussianMixture c θ x|) :=
    (finiteGaussianMixture_integrable c θ).abs
  have hright : Integrable (finiteGaussianMixture (fun i ↦ |c i|) θ) :=
    finiteGaussianMixture_integrable (fun i ↦ |c i|) θ
  have hdom : ∀ x,
      |finiteGaussianMixture c θ x| ≤
        finiteGaussianMixture (fun i ↦ |c i|) θ x := by
    intro x
    unfold finiteGaussianMixture
    calc
      |∑ i, c i * gaussianKernel d x (θ i)| ≤
          ∑ i, |c i * gaussianKernel d x (θ i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |c i| * gaussianKernel d x (θ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (gaussianKernel_pos d x (θ i))]
  calc
    (∫ x, |finiteGaussianMixture c θ x|) ≤
        ∫ x, finiteGaussianMixture (fun i ↦ |c i|) θ x := by
      exact integral_mono hleft hright hdom
    _ = ∑ i, |c i| := integral_finiteGaussianMixture _ _
