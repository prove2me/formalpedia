-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_finiteGaussianMixture_same_weights_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:06:01.018612+00:00
-- url     : https://prove2.me/submissions/e1887fe8-ab7c-4708-af92-6ae09ddb6fa2

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
import Theorems.Thm_ReweightedNPMLE_sqrt_sub_sq_finiteGaussianMixture_le_sum

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

























theorem continuous_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) : Continuous (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture gaussianKernel
  fun_prop

theorem finiteGaussianMixture_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    0 ≤ finiteGaussianMixture w θ x := by
  unfold finiteGaussianMixture
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le









/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ



/-- Every finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_integrable {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    Integrable (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (gaussianKernel_integrable d (θ i)).const_mul (w i)





















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

















/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]







































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
theorem solution {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
      ∑ i, w i * hellingerSq volume
        (fun x ↦ gaussianKernel d x (θ i))
        (fun x ↦ gaussianKernel d x (η i)) := by
  have hleft : Integrable (fun x : Point d ↦
      (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2) :=
    hellingerIntegrand_integrable_of_integrable volume
      (finiteGaussianMixture w θ) (finiteGaussianMixture w η)
      (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
      (continuous_finiteGaussianMixture w η).aestronglyMeasurable
      (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg θ hw))
      (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg η hw))
      (finiteGaussianMixture_integrable w θ)
      (finiteGaussianMixture_integrable w η)
  have hcomponent (i : ι) : Integrable (fun x : Point d ↦
      w i * (Real.sqrt (gaussianKernel d x (θ i)) -
        Real.sqrt (gaussianKernel d x (η i))) ^ 2) := by
    apply Integrable.const_mul
    exact hellingerIntegrand_integrable_of_integrable volume
      (fun x ↦ gaussianKernel d x (θ i)) (fun x ↦ gaussianKernel d x (η i))
      ((continuous_gaussianKernel d).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      ((continuous_gaussianKernel d).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianKernel_pos d x (θ i)).le)
      (Filter.Eventually.of_forall fun x ↦ (gaussianKernel_pos d x (η i)).le)
      (gaussianKernel_integrable d (θ i)) (gaussianKernel_integrable d (η i))
  have hright : Integrable (fun x : Point d ↦
      ∑ i, w i * (Real.sqrt (gaussianKernel d x (θ i)) -
        Real.sqrt (gaussianKernel d x (η i))) ^ 2) :=
    integrable_finsetSum Finset.univ fun i _ ↦ hcomponent i
  unfold hellingerSq
  calc
    (∫ x : Point d, (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2) ≤
        ∫ x : Point d, ∑ i, w i *
          (Real.sqrt (gaussianKernel d x (θ i)) -
            Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      exact integral_mono hleft hright
        (sqrt_sub_sq_finiteGaussianMixture_le_sum w θ η hw)
    _ = ∑ i, ∫ x : Point d, w i *
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      exact integral_finsetSum Finset.univ fun i _ ↦ hcomponent i
    _ = ∑ i, w i * ∫ x : Point d,
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
