-- Prove2me | solution 1 for ReweightedNPMLE.probability_optimizer_not_extreme_of_disjoint_positive_regions
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:00:57.048006+00:00
-- url     : https://prove2.me/submissions/fabf5216-96c8-4b95-9c9d-00d5138c0075

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
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation
import Theorems.Thm_ReweightedNPMLE_probability_optimizer_likelihood_contact_ae

-- Inline helpers preserved from ReweightedNPMLE.FittedContact.
section
/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE




  


@[simp] theorem likelihoodContactFunctional_apply {n : ℕ}
    (w v a : Fin n → ℝ) :
    likelihoodContactFunctional w v a =
      ∑ i, w i / (v i * total w) * a i := by
  simp [likelihoodContactFunctional]











end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ExtremeSupportPartition.
section
/-!
# Too many disjoint positive-mass regions prevent extremality

The contact identity converts zero fitted moments into zero mass. A finite
linear dependence among restricted evaluation moments gives a bounded
nonzero perturbation, hence a nontrivial decomposition of the full optimizer.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem integral_perturbation_eq_zero_of_contact_zero_moments {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (μ : ProbabilityMeasure Θ) (w v : Fin n → ℝ)
    (hcontact : (fun x ↦ likelihoodContactFunctional w v (A x)) =ᵐ[(μ : Measure Θ)] fun _ ↦ 1)
    (h : Θ → ℝ) (hhmeas : Measurable h) (M : ℝ) (hhbound : ∀ x, |h x| ≤ M)
    (hhmoment : ∀ i, ∫ x, h x * A x i ∂μ = 0) :
    ∫ x, h x ∂μ = 0 := by
  have hi : ∀ i, Integrable (fun x ↦ h x * A x i) (μ : Measure Θ) := fun i ↦
    (((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))).bdd_mul
      hhmeas.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hhbound x)
  calc
    (∫ x, h x ∂μ) = ∫ x, h x * likelihoodContactFunctional w v (A x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcontact] with x hx
      rw [hx, mul_one]
    _ = ∑ i, w i / (v i * total w) * (∫ x, h x * A x i ∂μ) := by
      simp only [likelihoodContactFunctional_apply, Finset.mul_sum]
      have heq : (fun x ↦ ∑ i, h x * (w i / (v i * total w) * A x i)) =
          fun x ↦ ∑ i, w i / (v i * total w) * (h x * A x i) := by
        funext x
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [heq, integral_finsetSum _ (fun i _ ↦ (hi i).const_mul _)]
      simp only [integral_const_mul]
    _ = 0 := by simp only [hhmoment, mul_zero, Finset.sum_const_zero]



end ReweightedNPMLE
end

/-!
# Too many disjoint positive-mass regions prevent extremality

The contact identity converts zero fitted moments into zero mass. A finite
linear dependence among restricted evaluation moments gives a bounded
nonzero perturbation, hence a nontrivial decomposition of the full optimizer.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n < m)
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (E : Fin m → Set Θ) (hE : ∀ j, MeasurableSet (E j))
    (hEd : Pairwise (fun j k ↦ Disjoint (E j) (E k))) (hEpos : ∀ j, 0 < (μ : Measure Θ) (E j)) :
    ¬ IsExtremeProbabilityMixture A v μ := by
  classical
  let B : Fin m → Fin n → ℝ := fun j i ↦ ∫ x in E j, A x i ∂μ
  have hBdep : ¬ LinearIndependent ℝ B := by
    intro hlin
    have hh : m ≤ n := by simpa using hlin.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, j₀, hcj⟩ := Fintype.not_linearIndependent_iff.mp hBdep
  let S : ℝ := ∑ j, |c j|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  let t : ℝ := 1 / (2 * (1 + S))
  have ht : 0 < t := by dsimp [t]; positivity
  let raw : Θ → ℝ := fun x ↦ ∑ j, (E j).indicator (fun _ ↦ c j) x
  let h : Θ → ℝ := fun x ↦ t * raw x
  have hrawMeas : Measurable raw := Finset.measurable_sum _
    (fun j _ ↦ measurable_const.indicator (hE j))
  have hhMeas : Measurable h := measurable_const.mul hrawMeas
  have hrawBound : ∀ x, |raw x| ≤ S := by
    intro x
    calc
      |raw x| ≤ ∑ j, |(E j).indicator (fun _ ↦ c j) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ S := Finset.sum_le_sum (fun j _ ↦ by
        by_cases hx : x ∈ E j
        · simp only [indicator_of_mem hx, le_refl]
        · simp only [indicator_of_notMem hx, abs_zero]
          exact abs_nonneg _)
  have hhBound : ∀ x, |h x| ≤ 1 / 2 := by
    intro x
    have hts : t * S ≤ 1 / 2 := by
      dsimp [t]
      field_simp
      nlinarith
    calc
      |h x| = t * |raw x| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ t * S := mul_le_mul_of_nonneg_left (hrawBound x) ht.le
      _ ≤ 1 / 2 := hts
  have hhMoment : ∀ i, ∫ x, h x * A x i ∂μ = 0 := by
    intro i
    have hAi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))
    change Integrable (fun x ↦ A x i) (μ : Measure Θ) at hAi
    have heq : (fun x ↦ h x * A x i) =
        fun x ↦ t * ∑ j, (E j).indicator (fun x ↦ c j * A x i) x := by
      funext x
      dsimp [h, raw]
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hx : x ∈ E j <;> simp [hx]
    rw [heq, integral_const_mul,
      integral_finsetSum _ (fun j _ ↦ (hAi.const_mul (c j)).indicator (hE j))]
    simp_rw [integral_indicator (hE _), integral_const_mul]
    have hi := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    change (∑ j, c j * ∫ x in E j, A x i ∂μ) = 0 at hi
    rw [hi, mul_zero]
  have hhMean : ∫ x, h x ∂μ = 0 := integral_perturbation_eq_zero_of_contact_zero_moments
    A hA μ w v (probability_optimizer_likelihood_contact_ae A hA hC hCpos hAC w v hw hvmax μ hμ)
    h hhMeas (1 / 2) hhBound hhMoment
  have hrawOn : ∀ x ∈ E j₀, raw x = c j₀ := by
    intro x hx
    dsimp [raw]
    rw [Finset.sum_eq_single j₀]
    · exact indicator_of_mem hx _
    · intro j _ hj
      have hxj : x ∉ E j := fun he ↦ (Set.disjoint_left.mp (hEd hj)) he hx
      exact indicator_of_notMem hxj _
    · simp
  have hhNonzero : ¬ h =ᵐ[(μ : Measure Θ)] fun _ ↦ 0 := by
    intro hhZero
    have hnot : ∀ᵐ x ∂(μ : Measure Θ), x ∉ E j₀ := hhZero.mono (fun x hx hxE ↦ by
      have hrawx := hrawOn x hxE
      change t * raw x = 0 at hx
      rw [hrawx] at hx
      exact hcj ((mul_eq_zero.mp hx).resolve_left ht.ne'))
    have hnull : (μ : Measure Θ) (E j₀) = 0 := by simpa only [ae_iff, not_not, setOf_mem_eq] using hnot
    exact (hEpos j₀).ne' hnull
  exact probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation
    A hA v μ hμ h hhMeas hhBound hhMean hhMoment hhNonzero
