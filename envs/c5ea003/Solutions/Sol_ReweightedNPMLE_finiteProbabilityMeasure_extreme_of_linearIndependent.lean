-- Prove2me | solution 1 for ReweightedNPMLE.finiteProbabilityMeasure_extreme_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:00:10.90812+00:00
-- url     : https://prove2.me/submissions/1d62e4fe-8939-4505-a5ba-6f309d7c5560

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
import Theorems.Thm_ReweightedNPMLE_isExtremeProbabilityMixture_iff
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_unique_of_supported_independent_range
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

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





theorem finiteProbabilityMeasure_ae_mem_range {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    ∀ᵐ x ∂(finiteProbabilityMeasure θ p hp : Measure Θ), x ∈ range θ := by
  change ∀ᵐ x ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j)), x ∈ range θ
  rw [ae_finsetSum_measure_iff]
  intro j _
  apply Measure.ae_smul_measure
  filter_upwards [ae_eq_dirac (fun x : Θ ↦ x)] with x hx
  rw [hx]
  exact mem_range_self j













theorem probabilityConvexCombination_left_absolutelyContinuous {Θ : Type*} [MeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (ha : 0 < a) (μ ν : ProbabilityMeasure Θ) :
    (μ : Measure Θ) ≪ (probabilityConvexCombination a b hab μ ν : Measure Θ) := by
  intro s hs
  change (a • (μ : Measure Θ) + b • (ν : Measure Θ)) s = 0 at hs
  rw [Measure.add_apply] at hs
  have hh := (add_eq_zero.mp hs).1
  rw [Measure.smul_apply] at hh
  change (a : ℝ≥0∞) * (μ : Measure Θ) s = 0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast ha.ne')







end ReweightedNPMLE
end

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
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m)
    (hlin : LinearIndependent ℝ (A ∘ θ)) :
    IsExtremeProbabilityMixture A (finiteMixtureValue (A ∘ θ) p) (finiteProbabilityMeasure θ p hp) := by
  let μ := finiteProbabilityMeasure θ p hp
  let v := finiteMixtureValue (A ∘ θ) p
  have hμ : μ ∈ probabilityMixtureFiber A v := probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp
  have hμS := finiteProbabilityMeasure_ae_mem_range θ p hp
  rw [isExtremeProbabilityMixture_iff]
  refine ⟨hμ, ?_⟩
  intro a b ha hb hab ν ρ hν hρ heq
  change probabilityConvexCombination a b hab ν ρ = μ at heq
  have hνac : (ν : Measure Θ) ≪ (μ : Measure Θ) := by
    rw [← heq]
    exact probabilityConvexCombination_left_absolutelyContinuous a b hab ha ν ρ
  exact probabilityMixtureFiber_unique_of_supported_independent_range A hA v θ hlin ν μ hν hμ
    (hνac.ae_le hμS) hμS
