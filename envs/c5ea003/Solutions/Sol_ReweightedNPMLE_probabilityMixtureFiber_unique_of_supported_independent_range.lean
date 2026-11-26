-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureFiber_unique_of_supported_independent_range
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:17.076044+00:00
-- url     : https://prove2.me/submissions/4f15e840-ab86-45a4-a560-91ea27eba7b8

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
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_probabilityMeasure_finiteRepresentation_of_ae_mem_range
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ]
    [OpensMeasurableSpace Θ] [MeasurableSingletonClass Θ] {m n : ℕ}
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (θ : Fin m → Θ) (hlin : LinearIndependent ℝ (A ∘ θ))
    (μ ν : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (hν : ν ∈ probabilityMixtureFiber A v)
    (hμS : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ)
    (hνS : ∀ᵐ x ∂(ν : Measure Θ), x ∈ range θ) : μ = ν := by
  have hθ : Function.Injective θ := fun j k hjk ↦ hlin.injective (congrArg A hjk)
  obtain ⟨p, hp, hpm⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ μ hμS
  obtain ⟨q, hq, hqn⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ ν hνS
  have hpeq : finiteMixtureValue (A ∘ θ) p = v := by
    rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp, hpm]
    exact hμ
  have hqeq : finiteMixtureValue (A ∘ θ) q = v := by
    rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ q hq, hqn]
    exact hν
  have hpq : p = q := hlin.fintypeLinearCombination_injective (hpeq.trans hqeq.symm)
  subst q
  exact hpm.symm.trans hqn
