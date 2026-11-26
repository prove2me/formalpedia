-- Prove2me | solution 1 for ReweightedNPMLE.probability_optimizer_likelihood_contact_ae
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:58.058712+00:00
-- url     : https://prove2.me/submissions/c08bdd95-84fa-4647-ac87-b33f20375131

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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_likelihoodContactFunctional_le_one_of_isMaxOn

-- Inline helpers preserved from ReweightedNPMLE.Weights.
section
/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

namespace ReweightedNPMLE























theorem total_pos {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : 0 < total w := by
  classical
  exact Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty

theorem total_ne_zero {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : total w ≠ 0 :=
  (total_pos hw).ne'



















end ReweightedNPMLE
end

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

/-- The fitted vector itself lies on the normalized contact hyperplane. -/
theorem likelihoodContactFunctional_self {n : ℕ} [Nonempty (Fin n)]
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    likelihoodContactFunctional w v v = 1 := by
  rw [likelihoodContactFunctional_apply]
  calc
    (∑ i, w i / (v i * total w) * v i) =
        ∑ i, w i / total w := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hv i).ne', (total_pos hw).ne']
    _ = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, total]
      exact mul_inv_cancel₀ (total_ne_zero hw)









end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityOptimizerFiber.
section
/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE































theorem integral_likelihoodContactFunctional {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (μ : ProbabilityMeasure Θ) (w v : Fin n → ℝ) :
    (∫ θ, likelihoodContactFunctional w v (A θ) ∂μ) =
      likelihoodContactFunctional w v (probabilityMixtureValue A μ) := by
  simp only [likelihoodContactFunctional_apply, probabilityMixtureValue]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
      |>.const_mul _





end ReweightedNPMLE
end

/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v) :
    (fun θ ↦ likelihoodContactFunctional w v (A θ)) =ᵐ[(μ : Measure Θ)] fun _ ↦ 1 := by
  have hq : Continuous (fun θ ↦ likelihoodContactFunctional w v (A θ)) := by
    simp only [likelihoodContactFunctional_apply]
    fun_prop
  have hqi := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (μ : Measure Θ))
  have hle : (fun θ ↦ likelihoodContactFunctional w v (A θ)) ≤ᵐ[(μ : Measure Θ)] fun _ ↦ 1 :=
    Eventually.of_forall fun θ ↦ likelihoodContactFunctional_le_one_of_isMaxOn
      hC hCpos w v (A θ) hw hvmax (hAC (mem_range_self θ))
  apply (integral_eq_iff_of_ae_le hqi (integrable_const 1) hle).mp
  rw [integral_likelihoodContactFunctional A hA μ w v, show probabilityMixtureValue A μ = v from hμ]
  simpa using likelihoodContactFunctional_self w v hw (hCpos hvmax.1)
