-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMeasure_finiteRepresentation_of_ae_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:53:39.155133+00:00
-- url     : https://prove2.me/submissions/8b1ef9d4-6a2d-41f0-b9ee-3ca8781661a6

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

theorem measure_eq_sum_dirac_of_ae_mem_range {Θ : Type*} [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] {m : ℕ} (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (μ : Measure Θ) (hμ : ∀ᵐ x ∂μ, x ∈ range θ) :
    μ = ∑ j, μ {θ j} • Measure.dirac (θ j) := by
  classical
  let S : Finset Θ := Finset.univ.image θ
  have hS : ∀ᵐ x ∂μ, x ∈ S := hμ.mono (fun x hx ↦ by simpa [S] using hx)
  have hh := Measure.ae_mem_finset_iff.mp hS
  dsimp [S] at hh
  rw [Finset.sum_image (fun j _ k _ hjk ↦ hθ hjk)] at hh
  exact hh

























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
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (μ : ProbabilityMeasure Θ)
    (hμ : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ) :
    ∃ (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m), finiteProbabilityMeasure θ p hp = μ := by
  let p : Fin m → ℝ := fun j ↦ (μ : Measure Θ).real {θ j}
  have hrepr := measure_eq_sum_dirac_of_ae_mem_range θ hθ (μ : Measure Θ) hμ
  have hsum : (∑ j, (μ : Measure Θ) {θ j}) = 1 := by
    have hh := congrArg (fun ρ : Measure Θ ↦ ρ univ) hrepr
    simpa only [measure_univ, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] using hh.symm
  have hp : p ∈ finiteSimplex m := by
    refine ⟨fun j ↦ measureReal_nonneg, ?_⟩
    dsimp [p, measureReal_def]
    rw [← ENNReal.toReal_sum (fun j _ ↦ measure_ne_top (μ : Measure Θ) {θ j}), hsum]
    norm_num
  refine ⟨p, hp, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change (∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j)) = (μ : Measure Θ)
  have hpcast : ∀ j, ENNReal.ofReal (p j) = (μ : Measure Θ) {θ j} := fun j ↦
    ENNReal.ofReal_toReal (measure_ne_top (μ : Measure Θ) {θ j})
  simp_rw [hpcast]
  exact hrepr.symm
