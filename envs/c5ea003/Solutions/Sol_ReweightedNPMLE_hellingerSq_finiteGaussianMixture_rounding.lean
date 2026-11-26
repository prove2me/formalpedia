-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_finiteGaussianMixture_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:06:45.733283+00:00
-- url     : https://prove2.me/submissions/357ab939-0d91-4178-a6e5-e8dba16d7ef5

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
import Theorems.Thm_ReweightedNPMLE_hellingerSq_eq_integrals
import Theorems.Thm_ReweightedNPMLE_hellingerSq_finiteGaussianMixture_same_locations_le_weight_l1
import Theorems.Thm_ReweightedNPMLE_hellingerSq_finiteGaussianMixture_same_weights_le_sum

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











/-- A squared triangle bound requiring only integrability of the three
square-root differences.  It is sufficient for the finite-net transfer and
avoids introducing an additional square-root-distance wrapper. -/
theorem hellingerSq_triangle_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q r : Ω → ℝ)
    (hpq : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hqr : Integrable (fun x ↦ (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2) μ)
    (hpr : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2) μ) :
    hellingerSq μ p r ≤ 2 * hellingerSq μ p q + 2 * hellingerSq μ q r := by
  unfold hellingerSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hpq.const_mul 2) (hqr.const_mul 2)]
  apply integral_mono_ae hpr ((hpq.const_mul 2).add (hqr.const_mul 2))
  exact Filter.Eventually.of_forall fun x ↦ by
    change (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2 ≤
      2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 +
        2 * (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2
    nlinarith [sq_nonneg ((Real.sqrt (p x) - Real.sqrt (q x)) -
      (Real.sqrt (q x) - Real.sqrt (r x)))]



























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































theorem sqrt_exp (t : ℝ) :
    Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  exact (Real.exp_half t).symm

theorem sqrt_gaussianKernel {d : ℕ} (x θ : Point d) :
    Real.sqrt (gaussianKernel d x θ) =
      Real.sqrt (gaussianConstant d) * Real.exp (-‖x - θ‖ ^ 2 / 4) := by
  unfold gaussianKernel
  rw [Real.sqrt_mul (gaussianConstant_pos d).le, sqrt_exp]
  congr 2
  ring

theorem sqrt_gaussianKernel_mul {d : ℕ} (x θ η : Point d) :
    Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η) =
      Real.exp (-‖θ - η‖ ^ 2 / 8) *
        gaussianKernel d x ((1 / 2 : ℝ) • (θ + η)) := by
  rw [Real.sqrt_mul (gaussianKernel_pos d x θ).le,
    sqrt_gaussianKernel, sqrt_gaussianKernel]
  unfold gaussianKernel
  have hθ : x - θ =
      (x - (1 / 2 : ℝ) • (θ + η)) - (1 / 2 : ℝ) • (θ - η) := by module
  have hη : x - η =
      (x - (1 / 2 : ℝ) • (θ + η)) + (1 / 2 : ℝ) • (θ - η) := by module
  have hpara := parallelogram_law_with_norm ℝ
    (x - (1 / 2 : ℝ) • (θ + η)) ((1 / 2 : ℝ) • (θ - η))
  have hexp : -‖x - θ‖ ^ 2 / 4 + -‖x - η‖ ^ 2 / 4 =
      -‖θ - η‖ ^ 2 / 8 +
        -‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2 := by
    rw [hθ, hη]
    rw [norm_smul] at hpara
    norm_num at hpara ⊢
    nlinarith
  have hc : Real.sqrt (gaussianConstant d) * Real.sqrt (gaussianConstant d) =
      gaussianConstant d := by
    rw [← pow_two, Real.sq_sqrt (gaussianConstant_pos d).le]
  calc
    (Real.sqrt (gaussianConstant d) * Real.exp (-‖x - θ‖ ^ 2 / 4)) *
        (Real.sqrt (gaussianConstant d) * Real.exp (-‖x - η‖ ^ 2 / 4)) =
        (Real.sqrt (gaussianConstant d) * Real.sqrt (gaussianConstant d)) *
          (Real.exp (-‖x - θ‖ ^ 2 / 4) * Real.exp (-‖x - η‖ ^ 2 / 4)) := by ring
    _ = gaussianConstant d * Real.exp
        (-‖θ - η‖ ^ 2 / 8 +
          -‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2) := by
      rw [hc, ← Real.exp_add, hexp]
    _ = Real.exp (-‖θ - η‖ ^ 2 / 8) *
        (gaussianConstant d *
          Real.exp (-‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2)) := by
      rw [Real.exp_add]
      ring

theorem gaussianKernel_sqrt_product_integrable {d : ℕ} (θ η : Point d) :
    Integrable (fun x : Point d ↦
      Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η)) := by
  apply ((gaussianKernel_integrable d ((1 / 2 : ℝ) • (θ + η))).const_mul
    (Real.exp (-‖θ - η‖ ^ 2 / 8))).congr
  exact Filter.Eventually.of_forall fun x ↦ (sqrt_gaussianKernel_mul x θ η).symm

/-- Exact Hellinger affinity of two translates of the standard Gaussian. -/
theorem hellingerAffinity_gaussianKernel {d : ℕ} (θ η : Point d) :
    hellingerAffinity volume (gaussianKernel d · θ) (gaussianKernel d · η) =
      Real.exp (-‖θ - η‖ ^ 2 / 8) := by
  unfold hellingerAffinity
  calc
    (∫ x : Point d,
        Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η)) =
        ∫ x : Point d, Real.exp (-‖θ - η‖ ^ 2 / 8) *
          gaussianKernel d x ((1 / 2 : ℝ) • (θ + η)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ sqrt_gaussianKernel_mul x θ η
    _ = Real.exp (-‖θ - η‖ ^ 2 / 8) := by
      rw [integral_const_mul, integral_gaussianKernel, mul_one]

/-- Exact squared Hellinger distance between two standard Gaussian
translates. -/
theorem hellingerSq_gaussianKernel {d : ℕ} (θ η : Point d) :
    hellingerSq volume (gaussianKernel d · θ) (gaussianKernel d · η) =
      2 * (1 - Real.exp (-‖θ - η‖ ^ 2 / 8)) := by
  rw [hellingerSq_eq_integrals volume (gaussianKernel d · θ)
    (gaussianKernel d · η)
    (fun x ↦ (gaussianKernel_pos d x θ).le)
    (fun x ↦ (gaussianKernel_pos d x η).le)
    (gaussianKernel_integrable d θ) (gaussianKernel_integrable d η)
    (gaussianKernel_sqrt_product_integrable θ η)]
  rw [integral_gaussianKernel, integral_gaussianKernel,
    hellingerAffinity_gaussianKernel]
  ring

theorem hellingerSq_gaussianKernel_le_norm_sq_div_four {d : ℕ}
    (θ η : Point d) :
    hellingerSq volume (gaussianKernel d · θ) (gaussianKernel d · η) ≤
      ‖θ - η‖ ^ 2 / 4 := by
  rw [hellingerSq_gaussianKernel]
  have hexp := Real.add_one_le_exp (-‖θ - η‖ ^ 2 / 8)
  nlinarith







theorem hellingerSq_finiteGaussianMixture_same_weights_le_location_sq {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
      ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) := by
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
        ∑ i, w i * hellingerSq volume
          (fun x ↦ gaussianKernel d x (θ i))
          (fun x ↦ gaussianKernel d x (η i)) :=
      hellingerSq_finiteGaussianMixture_same_weights_le_sum w θ η hw
    _ ≤ ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (hellingerSq_gaussianKernel_le_norm_sq_div_four (θ i) (η i)) (hw i)

theorem hellingerSq_finiteGaussianMixture_location_rounding {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hloc : ∀ i, ‖θ i - η i‖ ≤ ε) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤ ε ^ 2 / 4 := by
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
        ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) :=
      hellingerSq_finiteGaussianMixture_same_weights_le_location_sq w θ η hw
    _ ≤ ∑ i, w i * (ε ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hε).2 (hloc i)) (by norm_num)
    _ = ε ^ 2 / 4 := by
      rw [← Finset.sum_mul, hwsum, one_mul]

theorem finiteGaussianMixture_hellingerIntegrable {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    Integrable (fun x : Point d ↦
      (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture v η x)) ^ 2) :=
  hellingerIntegrand_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v η)
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
    (continuous_finiteGaussianMixture v η).aestronglyMeasurable
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg θ hw))
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg η hv))
    (finiteGaussianMixture_integrable w θ)
    (finiteGaussianMixture_integrable v η)



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
/-- Simultaneously rounding every location and every mass gives the two
explicit error terms needed by the finite likelihood-net construction. -/
theorem solution {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hloc : ∀ i, ‖θ i - η i‖ ≤ ε) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture v η) ≤
      ε ^ 2 / 2 + 2 * ∑ i, |w i - v i| := by
  have htri := hellingerSq_triangle_bound volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture w η)
    (finiteGaussianMixture v η)
    (finiteGaussianMixture_hellingerIntegrable w w θ η hw hw)
    (finiteGaussianMixture_hellingerIntegrable w v η η hw hv)
    (finiteGaussianMixture_hellingerIntegrable w v θ η hw hv)
  have hlocH := hellingerSq_finiteGaussianMixture_location_rounding
    w θ η hw hwsum hε hloc
  have hmassH := hellingerSq_finiteGaussianMixture_same_locations_le_weight_l1
    w v η hw hv hwsum hvsum
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture v η) ≤
        2 * hellingerSq volume (finiteGaussianMixture w θ)
            (finiteGaussianMixture w η) +
          2 * hellingerSq volume (finiteGaussianMixture w η)
            (finiteGaussianMixture v η) := htri
    _ ≤ 2 * (ε ^ 2 / 4) + 2 * ∑ i, |w i - v i| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlocH (by norm_num))
        (mul_le_mul_of_nonneg_left hmassH (by norm_num))
    _ = ε ^ 2 / 2 + 2 * ∑ i, |w i - v i| := by ring
