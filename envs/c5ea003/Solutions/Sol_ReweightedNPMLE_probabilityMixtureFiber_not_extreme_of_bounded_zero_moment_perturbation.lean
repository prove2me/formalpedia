-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:18.796536+00:00
-- url     : https://prove2.me/submissions/0403add6-fe3c-4ae9-b5a4-1c33c0b07e01

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_isExtremeProbabilityMixture_iff

-- Inline helpers preserved from ReweightedNPMLE.MeasureFiberPerturbation.
section
/-!
# Moment-preserving perturbations of probability measures

A bounded nonzero perturbation with zero mass and zero fitted moments gives
two genuine probability measures in the same full fiber whose average is
the original law. This applies to arbitrary, possibly infinite-support laws.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE



theorem integral_probabilityMeasureWithRealDensity {Θ : Type*} [MeasurableSpace Θ]
    (μ : ProbabilityMeasure Θ) (f : Θ → ℝ) (hf : Integrable f (μ : Measure Θ))
    (hf₀ : ∀ x, 0 ≤ f x) (hfmean : ∫ x, f x ∂μ = 1)
    (hfmeas : Measurable f) (g : Θ → ℝ) :
    (∫ x, g x ∂probabilityMeasureWithRealDensity μ f hf hf₀ hfmean) =
      ∫ x, f x * g x ∂μ := by
  change (∫ x, g x ∂(μ : Measure Θ).withDensity (fun x ↦ ENNReal.ofReal (f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hfmeas.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf₀ _), smul_eq_mul]



end ReweightedNPMLE
end

/-!
# Moment-preserving perturbations of probability measures

A bounded nonzero perturbation with zero mass and zero fitted moments gives
two genuine probability measures in the same full fiber whose average is
the original law. This applies to arbitrary, possibly infinite-support laws.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (h : Θ → ℝ) (hhmeas : Measurable h) (hhbound : ∀ x, |h x| ≤ 1 / 2)
    (hhmean : ∫ x, h x ∂μ = 0)
    (hhmoment : ∀ i, ∫ x, h x * A x i ∂μ = 0)
    (hhnonzero : ¬ h =ᵐ[(μ : Measure Θ)] fun _ ↦ 0) :
    ¬ IsExtremeProbabilityMixture A v μ := by
  let fPlus : Θ → ℝ := fun x ↦ 1 + h x
  let fMinus : Θ → ℝ := fun x ↦ 1 - h x
  have hhi : Integrable h (μ : Measure Θ) := Integrable.of_bound hhmeas.aestronglyMeasurable
    (1 / 2) (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hhbound x)
  have hplus : ∀ x, 0 ≤ fPlus x := fun x ↦ by
    have hx := neg_le_of_abs_le (hhbound x)
    dsimp [fPlus]
    linarith
  have hminus : ∀ x, 0 ≤ fMinus x := fun x ↦ by
    have hx := le_of_abs_le (hhbound x)
    dsimp [fMinus]
    linarith
  have hplusI : Integrable fPlus (μ : Measure Θ) := (integrable_const 1).add hhi
  have hminusI : Integrable fMinus (μ : Measure Θ) := (integrable_const 1).sub hhi
  have hplusM : ∫ x, fPlus x ∂μ = 1 := by
    rw [integral_add (integrable_const 1) hhi, hhmean]
    simp
  have hminusM : ∫ x, fMinus x ∂μ = 1 := by
    rw [integral_sub (integrable_const 1) hhi, hhmean]
    simp
  have hplusMeas : Measurable fPlus := measurable_const.add hhmeas
  have hminusMeas : Measurable fMinus := measurable_const.sub hhmeas
  let ν := probabilityMeasureWithRealDensity μ fPlus hplusI hplus hplusM
  let ρ := probabilityMeasureWithRealDensity μ fMinus hminusI hminus hminusM
  have hνval : ν ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A ν = v
    funext i
    have hAi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))
    change Integrable (fun x ↦ A x i) (μ : Measure Θ) at hAi
    have hhAi : Integrable (fun x ↦ h x * A x i) (μ : Measure Θ) :=
      hAi.bdd_mul hhmeas.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hhbound x)
    change (∫ x, A x i ∂ν) = v i
    rw [integral_probabilityMeasureWithRealDensity μ fPlus hplusI hplus hplusM hplusMeas]
    simp_rw [fPlus, add_mul, one_mul]
    rw [integral_add hAi hhAi, hhmoment i, add_zero]
    exact congrFun hμ i
  have hρval : ρ ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A ρ = v
    funext i
    have hAi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))
    change Integrable (fun x ↦ A x i) (μ : Measure Θ) at hAi
    have hhAi : Integrable (fun x ↦ h x * A x i) (μ : Measure Θ) :=
      hAi.bdd_mul hhmeas.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hhbound x)
    change (∫ x, A x i ∂ρ) = v i
    rw [integral_probabilityMeasureWithRealDensity μ fMinus hminusI hminus hminusM hminusMeas]
    simp_rw [fMinus, sub_mul, one_mul]
    rw [integral_sub hAi hhAi, hhmoment i, sub_zero]
    exact congrFun hμ i
  have havg : probabilityConvexCombination (1 / 2) (1 / 2) (by norm_num) ν ρ = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    change (1 / 2 : ℝ≥0) • (μ : Measure Θ).withDensity (fun x ↦ ENNReal.ofReal (fPlus x)) +
      (1 / 2 : ℝ≥0) • (μ : Measure Θ).withDensity (fun x ↦ ENNReal.ofReal (fMinus x)) = (μ : Measure Θ)
    rw [← smul_add, ← withDensity_add_left hplusMeas.ennreal_ofReal]
    have hsum : (fun x ↦ ENNReal.ofReal (fPlus x)) + (fun x ↦ ENNReal.ofReal (fMinus x)) =
        fun _ ↦ (2 : ℝ≥0∞) := by
      funext x
      rw [Pi.add_apply, ← ENNReal.ofReal_add (hplus x) (hminus x)]
      norm_num [fPlus, fMinus]
    rw [hsum, withDensity_const]
    rw [ENNReal.smul_def, smul_smul]
    norm_num
    rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num), one_smul]
  intro hext
  have hνeq := (isExtremeProbabilityMixture_iff A v μ).mp hext |>.2
    (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) ν ρ hνval hρval havg
  have hdensity : (fun x ↦ ENNReal.ofReal (fPlus x)) =ᵐ[(μ : Measure Θ)] fun _ ↦ 1 := by
    apply (withDensity_eq_iff_of_sigmaFinite hplusMeas.ennreal_ofReal.aemeasurable
      measurable_const.aemeasurable).mp
    change (ν : Measure Θ) = (μ : Measure Θ).withDensity (fun _ ↦ 1)
    rw [hνeq]
    exact withDensity_one.symm
  apply hhnonzero
  filter_upwards [hdensity] with x hx
  have hr := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal (hplus x)] at hr
  norm_num [fPlus] at hr
  linarith
