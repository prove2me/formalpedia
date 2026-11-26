-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_finiteGaussianMixture_same_locations_le_weight_l1
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:57.4485+00:00
-- url     : https://prove2.me/submissions/4972dd99-dc6b-44f6-a66b-a91569f57c74

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
import Theorems.Thm_ReweightedNPMLE_integral_abs_finiteGaussianMixture_le_sum_abs
import Theorems.Thm_ReweightedNPMLE_sqrt_sub_sq_le_abs_sub

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



theorem finiteGaussianMixture_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Point d) :
    0 < finiteGaussianMixture w θ x := by
  have hsumpos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) ↦ hw i).mp hsumpos
  unfold finiteGaussianMixture
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (gaussianKernel_pos d x (θ j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (gaussianKernel_pos d x (θ i))⟩







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









/-- Consequently squared Hellinger distance is at most `L¹` distance. -/
theorem hellingerSq_le_integral_abs_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hhell : Integrable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hl1 : Integrable (fun x ↦ |p x - q x|) μ) :
    hellingerSq μ p q ≤ ∫ x, |p x - q x| ∂μ := by
  unfold hellingerSq
  apply integral_mono_ae hhell hl1
  filter_upwards [hp, hq] with x hpx hqx
  exact sqrt_sub_sq_le_abs_sub hpx hqx







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





theorem abs_sub_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ |p x - q x|) μ := by
  exact (hpint.sub hqint).abs

































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureHellinger.
section
/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE



























theorem finiteGaussianMixture_sub_same_locations
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    finiteGaussianMixture w θ x - finiteGaussianMixture v θ x =
      finiteGaussianMixture (fun i ↦ w i - v i) θ x := by
  unfold finiteGaussianMixture
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring































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
/-- Rounding only the masses of a finite probability mixture changes squared
Hellinger distance by at most the `ℓ¹` mass error. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1) :
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) ≤
      ∑ i, |w i - v i| := by
  have hpint := finiteGaussianMixture_integrable w θ
  have hqint := finiteGaussianMixture_integrable v θ
  have hp : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture w θ x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos θ hw hwsum x).le
  have hq : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture v θ x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos θ hv hvsum x).le
  have hhell := hellingerIntegrand_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v θ)
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
    (continuous_finiteGaussianMixture v θ).aestronglyMeasurable
    hp hq hpint hqint
  have hl1 := abs_sub_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) hpint hqint
  calc
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) ≤
        ∫ x, |finiteGaussianMixture w θ x - finiteGaussianMixture v θ x| :=
      hellingerSq_le_integral_abs_sub volume _ _ hp hq hhell hl1
    _ = ∫ x, |finiteGaussianMixture (fun i ↦ w i - v i) θ x| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change |finiteGaussianMixture w θ x - finiteGaussianMixture v θ x| =
          |finiteGaussianMixture (fun i ↦ w i - v i) θ x|
        rw [finiteGaussianMixture_sub_same_locations]
    _ ≤ ∑ i, |w i - v i| :=
      integral_abs_finiteGaussianMixture_le_sum_abs _ _
