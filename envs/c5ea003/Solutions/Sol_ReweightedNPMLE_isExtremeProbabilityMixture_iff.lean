-- Prove2me | solution 1 for ReweightedNPMLE.isExtremeProbabilityMixture_iff
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:53:33.219089+00:00
-- url     : https://prove2.me/submissions/380b517a-013b-4d06-b510-41af43ec8c9d

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
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

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

theorem probabilityIntegralFunctional_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityIntegralFunctional (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityIntegralFunctional μ + (b : ℝ) • probabilityIntegralFunctional ν := by
  funext f
  have hμ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (μ : Measure Θ))
  have hν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (ν : Measure Θ))
  change (∫ θ, f θ ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityIntegralFunctional, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl









theorem isExtremeProbabilityMixture_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A v μ) : μ ∈ probabilityMixtureFiber A v := by
  obtain ⟨ν, hν, heq⟩ := hμ.1
  exact probabilityIntegralFunctional_injective heq ▸ hν









end ReweightedNPMLE
end

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

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [HasOuterApproxClosed Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔ μ ∈ probabilityMixtureFiber A v ∧
      ∀ (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
        (ν ρ : ProbabilityMeasure Θ), ν ∈ probabilityMixtureFiber A v →
        ρ ∈ probabilityMixtureFiber A v →
        probabilityConvexCombination a b hab ν ρ = μ → ν = μ := by
  constructor
  · intro hμ
    refine ⟨isExtremeProbabilityMixture_mem_fiber A v μ hμ, ?_⟩
    intro a b ha hb hab ν ρ hν hρ heq
    apply probabilityIntegralFunctional_injective
    apply (mem_extremePoints_iff_left.mp hμ).2 _ ⟨ν, hν, rfl⟩ _ ⟨ρ, hρ, rfl⟩
    refine ⟨(a : ℝ), (b : ℝ), by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hab, ?_⟩
    rw [← probabilityIntegralFunctional_convexCombination a b hab ν ρ, heq]
  · rintro ⟨hμ, huniq⟩
    refine ⟨⟨μ, hμ, rfl⟩, ?_⟩
    rintro x ⟨ν, hν, rfl⟩ y ⟨ρ, hρ, rfl⟩ ⟨a, b, ha, hb, hab, hrepr⟩
    let a' : ℝ≥0 := ⟨a, ha.le⟩
    let b' : ℝ≥0 := ⟨b, hb.le⟩
    have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
    have heq : probabilityConvexCombination a' b' hab' ν ρ = μ := by
      apply probabilityIntegralFunctional_injective
      rw [probabilityIntegralFunctional_convexCombination a' b' hab' ν ρ]
      exact hrepr
    exact congrArg probabilityIntegralFunctional
      (huniq a' b' (by exact_mod_cast ha) (by exact_mod_cast hb) hab' ν ρ hν hρ heq)
