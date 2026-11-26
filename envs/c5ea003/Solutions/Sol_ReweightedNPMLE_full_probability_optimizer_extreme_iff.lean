-- Prove2me | solution 1 for ReweightedNPMLE.full_probability_optimizer_extreme_iff
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:54.356601+00:00
-- url     : https://prove2.me/submissions/2e1d3c71-e334-41a7-9e58-35dd810f3290

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
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
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
import Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_extreme_of_linearIndependent
import Theorems.Thm_ReweightedNPMLE_finite_probability_optimizer_extreme_iff_linearIndependent
import Theorems.Thm_ReweightedNPMLE_full_extreme_optimizer_support_finite_card_le
import Theorems.Thm_ReweightedNPMLE_probabilityMeasure_positive_finiteRepresentation_of_finite_support
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityFiberGeometry.
section
/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





theorem probabilityIntegralFunctional_injective {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    Function.Injective (probabilityIntegralFunctional (Θ := Θ)) := by
  intro μ ν h
  have hh : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f ↦ congrFun h f.toContinuousMap)
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun ρ : FiniteMeasure Θ ↦ (ρ : Measure Θ)) hh











theorem isExtremeProbabilityMixture_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A v μ) : μ ∈ probabilityMixtureFiber A v := by
  obtain ⟨ν, hν, heq⟩ := hμ.1
  exact probabilityIntegralFunctional_injective heq ▸ hν









end ReweightedNPMLE
end

/-!
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The complete full-measure extreme-optimizer characterization. In
particular, finite support and the `n`-atom bound are conclusions, not
hypotheses. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔
      ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
        k ≤ n ∧ Function.Injective θ ∧ (∀ j, 0 < p j) ∧ LinearIndependent ℝ (A ∘ θ) ∧
          finiteMixtureValue (A ∘ θ) p = v ∧ finiteProbabilityMeasure θ p hp = μ := by
  constructor
  · intro hext
    have hμ := isExtremeProbabilityMixture_mem_fiber A v μ hext
    have hsupport := full_extreme_optimizer_support_finite_card_le A hA hC hCpos hAC w v hw hvmax μ hext
    obtain ⟨k, θ, p, hp, hkcard, hθ, hRange, hpPos, heq⟩ :=
      probabilityMeasure_positive_finiteRepresentation_of_finite_support μ hsupport.1
    have hpval : finiteMixtureValue (A ∘ θ) p = v := by
      rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp, heq]
      exact hμ
    have hpf : p ∈ finiteMixtureFiber (A ∘ θ) v := ⟨hp, hpval⟩
    have hvHull : v ∈ convexHull ℝ (range (A ∘ θ)) :=
      mem_convexHull_iff_exists_fintype.mpr
        ⟨Fin k, inferInstance, p, A ∘ θ, hp.1, hp.2, (fun j ↦ mem_range_self j), hpval⟩
    have hHullC : convexHull ℝ (range (A ∘ θ)) ⊆ C :=
      convexHull_min (fun a ha ↦ by rcases ha with ⟨j, rfl⟩; exact hAC (mem_range_self (θ j))) hC
    have hvmaxFinite : IsMaxOn (convexHull ℝ (range (A ∘ θ))) (weightedLogLikelihood w) v :=
      ⟨hvHull, fun a ha ↦ hvmax.2 a (hHullC ha)⟩
    have hextFinite : IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hpf.1) := by
      simpa only [heq] using hext
    have hlin := (finite_probability_optimizer_extreme_iff_linearIndependent A hA θ hθ v p hpf hpPos
      w hw (hCpos hvmax.1) (fun j ↦ hCpos (hAC (mem_range_self (θ j)))) hvmaxFinite).mp hextFinite
    exact ⟨k, θ, p, hp, hkcard ▸ hsupport.2, hθ, hpPos, hlin, hpval, heq⟩
  · rintro ⟨k, θ, p, hp, hk, hθ, hpPos, hlin, hpval, heq⟩
    have hext := finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp hlin
    simpa only [hpval, heq] using hext
