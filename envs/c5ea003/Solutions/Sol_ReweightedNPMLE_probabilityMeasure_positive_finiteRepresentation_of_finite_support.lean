-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMeasure_positive_finiteRepresentation_of_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:21.850425+00:00
-- url     : https://prove2.me/submissions/3b06cc5b-35e2-4a0a-991e-850dd36f05e9

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
import Theorems.Thm_ReweightedNPMLE_probabilityMeasure_finiteRepresentation_of_ae_mem_range

-- Inline helpers preserved from ReweightedNPMLE.FiniteProbabilityExtreme.
section
/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE







theorem finiteProbabilityMeasure_singleton_mass {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (j : Fin m) :
    (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} = ENNReal.ofReal (p j) := by
  classical
  change (∑ k, ENNReal.ofReal (p k) • Measure.dirac (θ k)) {θ j} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hneq : θ k ≠ θ j := fun hh ↦ hkj (hθ hh)
    simp [hneq]
  · simp



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FullExtremeSupport.
section
/-!
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE







theorem measure_support_singleton_pos_of_finite_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : Measure Θ) (hs : μ.support.Finite) (x : Θ) (hx : x ∈ μ.support) :
    0 < μ {x} := by
  by_contra hpos
  have hzero : μ {x} = 0 := le_antisymm (not_lt.mp hpos) bot_le
  have hAE : ∀ᵐ a ∂μ, a ∈ μ.support \ {x} := by
    filter_upwards [μ.support_mem_ae, measure_eq_zero_iff_ae_notMem.mp hzero] with a ha hax
    exact ⟨ha, hax⟩
  have hsub := μ.support_subset_of_isClosed (hs.diff (t := {x})).isClosed hAE
  have hh := hsub hx
  exact hh.2 (mem_singleton x)





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
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : ProbabilityMeasure Θ) (hs : (μ : Measure Θ).support.Finite) :
    ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
      k = (μ : Measure Θ).support.ncard ∧ Function.Injective θ ∧
      range θ = (μ : Measure Θ).support ∧ (∀ j, 0 < p j) ∧ finiteProbabilityMeasure θ p hp = μ := by
  classical
  let T := (μ : Measure Θ).support
  letI : Fintype T := hs.fintype
  let k := Fintype.card T
  let e : Fin k ≃ T := (Fintype.equivFin T).symm
  let θ : Fin k → Θ := fun j ↦ (e j).val
  have hθ : Function.Injective θ := fun j l hjl ↦ e.injective (Subtype.ext hjl)
  have hRange : range θ = T := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e j).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hAE : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ := by
    rw [hRange]
    exact (μ : Measure Θ).support_mem_ae
  obtain ⟨p, hp, heq⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ μ hAE
  have hpPos : ∀ j, 0 < p j := by
    intro j
    have hj : 0 < (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} := by
      rw [heq]
      exact measure_support_singleton_pos_of_finite_support (μ : Measure Θ) hs (θ j) (e j).property
    rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp] at hj
    exact ENNReal.ofReal_pos.mp hj
  refine ⟨k, θ, p, hp, ?_, hθ, hRange, hpPos, heq⟩
  change Fintype.card T = T.ncard
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
