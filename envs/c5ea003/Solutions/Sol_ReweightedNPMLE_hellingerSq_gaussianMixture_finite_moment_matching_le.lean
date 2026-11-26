-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_gaussianMixture_finite_moment_matching_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:10:03.820425+00:00
-- url     : https://prove2.me/submissions/dddbf5d0-ee19-4a51-adc7-d722334d5b21

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
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_sq_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_general_finite_moment_matching_weightedL2_bound
import Theorems.Thm_ReweightedNPMLE_integral_abs_le_sqrt_weightedL2
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

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasure.
section
/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem gaussianMixture_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (gaussianMixture μ θ) := by
  exact (gaussianKernel_comp_integrable_prod μ θ hθ).integral_prod_right

























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



/-- For a normalized positive reference density, weighted `L²` error bounds
squared Hellinger distance by its square root. -/
theorem hellingerSq_le_sqrt_weightedL2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q φ : Ω → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpqmeas : AEStronglyMeasurable (fun x ↦ p x - q x) μ)
    (hφmeas : AEStronglyMeasurable φ μ)
    (hφpos : ∀ᵐ x ∂μ, 0 < φ x)
    (hhell : Integrable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hl1 : Integrable (fun x ↦ |p x - q x|) μ)
    (hweighted : Integrable (fun x ↦ (p x - q x) ^ 2 / φ x) μ)
    (hφint : Integrable φ μ) (hφone : ∫ x, φ x ∂μ = 1) :
    hellingerSq μ p q ≤
      (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) := by
  calc
    hellingerSq μ p q ≤ ∫ x, |p x - q x| ∂μ :=
      hellingerSq_le_integral_abs_sub μ p q hp hq hhell hl1
    _ ≤ (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) :=
      integral_abs_le_sqrt_weightedL2 μ (fun x ↦ p x - q x) φ
        hpqmeas hφmeas hφpos hweighted hφint
    _ = (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) := by
      rw [hφone]
      norm_num



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





theorem gaussianMixture_sub_finite_sq_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    Integrable (fun x : Point d ↦
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x) := by
  have hp := gaussianMixture_sq_div_density_integrable μ θ hθmeas hS hθS
  have hpq := gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hq := finiteGaussianMixture_sq_div_density_integrable w z
  apply (hp.sub (hpq.const_mul 2) |>.add hq).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
        (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x =
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x
    ring

































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
/-- Squared-Hellinger consequence of moment matching for an arbitrary
probability mixing law and a finite probability law. -/
theorem solution
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    hellingerSq volume (gaussianMixture μ θ) (finiteGaussianMixture w z) ≤
      (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial)) ^ (1 / 2 : ℝ) := by
  have hpint := gaussianMixture_integrable μ θ hθmeas
  have hqint := finiteGaussianMixture_integrable w z
  have hpmeas : AEStronglyMeasurable (gaussianMixture μ θ)
      (volume : Measure (Point d)) := hpint.aestronglyMeasurable
  have hqmeas : AEStronglyMeasurable (finiteGaussianMixture w z)
      (volume : Measure (Point d)) :=
    (continuous_finiteGaussianMixture w z).aestronglyMeasurable
  have hp : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ gaussianMixture μ θ x :=
    Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos μ θ hθmeas x).le
  have hq : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture w z x :=
    Filter.Eventually.of_forall fun x ↦
      (finiteGaussianMixture_pos z hw hwsum x).le
  have hhell := hellingerIntegrand_integrable_of_integrable
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z)
      hpmeas hqmeas hp hq hpint hqint
  have hl1 := abs_sub_integrable_of_integrable
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z) hpint hqint
  have hweighted := gaussianMixture_sub_finite_sq_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hH := hellingerSq_le_sqrt_weightedL2
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z)
      (gaussianDensity d) hp hq (hpmeas.sub hqmeas)
      (continuous_gaussianDensity d).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ gaussianDensity_pos d x)
      hhell hl1 hweighted (gaussianDensity_integrable d)
      (integral_gaussianDensity d)
  have hQnonneg : 0 ≤ ∫ x : Point d,
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x := by
    apply integral_nonneg
    intro x
    exact div_nonneg (sq_nonneg _) (gaussianDensity_pos d x).le
  have hQbound := general_finite_moment_matching_weightedL2_bound
    μ θ hθmeas w z hw hwsum hint hmom hS hθS hzS
  exact hH.trans (Real.rpow_le_rpow hQnonneg hQbound (by norm_num))
