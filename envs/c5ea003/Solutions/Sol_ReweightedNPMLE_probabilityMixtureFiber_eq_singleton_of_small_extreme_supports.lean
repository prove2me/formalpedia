-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_small_extreme_supports
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:25.992508+00:00
-- url     : https://prove2.me/submissions/dc1b2910-a22d-44cc-a3c2-5ff991031c13

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_full_extreme_optimizer_support_finite_card_le
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_eq_singleton_of_extreme_unique
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_unique_of_supported_independent_range

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
# Uniqueness from small extreme supports and evaluation independence

Two extreme laws are concentrated on the union of their finite supports.
Independence on that union forces equality; the full-measure Krein--Milman
theorem then makes the whole optimizer fiber a singleton. This does not assume
finite support of non-extreme optimizing measures.
-/

open Set MeasureTheory
open scoped Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n m L : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (hvHull : v ∈ convexHull ℝ (range A)) (hsize : 2 * m ≤ L)
    (hind : ∀ (k : ℕ), k ≤ L → ∀ θ : Fin k → Θ,
      Function.Injective θ → LinearIndependent ℝ (A ∘ θ))
    (hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A v μ →
      (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ ∧ (μ : Measure Θ).support.Finite ∧
        (μ : Measure Θ).support.ncard ≤ m := by
  classical
  have hunique : ∀ μ ν : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture A v μ → IsExtremeProbabilityMixture A v ν → μ = ν := by
    intro μ ν hμext hνext
    have hμfinite := (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
      hAC w v hw hvmax μ hμext).1
    have hνfinite := (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
      hAC w v hw hvmax ν hνext).1
    let T := (μ : Measure Θ).support ∪ (ν : Measure Θ).support
    have hTfinite : T.Finite := hμfinite.union hνfinite
    letI : Fintype T := hTfinite.fintype
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
    have hk : k ≤ L := by
      have hcard : k = T.ncard := by
        change Fintype.card T = T.ncard
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      rw [hcard]
      exact (ncard_union_le _ _).trans
        ((Nat.add_le_add (hsmall μ hμext) (hsmall ν hνext)).trans (by omega))
    have hμAE : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ := by
      rw [hRange]
      filter_upwards [(μ : Measure Θ).support_mem_ae] with x hx
      exact Or.inl hx
    have hνAE : ∀ᵐ x ∂(ν : Measure Θ), x ∈ range θ := by
      rw [hRange]
      filter_upwards [(ν : Measure Θ).support_mem_ae] with x hx
      exact Or.inr hx
    exact probabilityMixtureFiber_unique_of_supported_independent_range A hA v θ (hind k hk θ hθ)
      μ ν (isExtremeProbabilityMixture_mem_fiber A v μ hμext)
      (isExtremeProbabilityMixture_mem_fiber A v ν hνext) hμAE hνAE
  obtain ⟨μ, hfiber, hext⟩ := probabilityMixtureFiber_eq_singleton_of_extreme_unique
    A hA v hvHull hunique
  exact ⟨μ, hfiber, hext, (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
    hAC w v hw hvmax μ hext).1, hsmall μ hext⟩
