-- Prove2me | solution 1 for ReweightedNPMLE.finiteProbabilityMeasure_support
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:56.743951+00:00
-- url     : https://prove2.me/submissions/59f55aad-c42c-4a70-8173-6ab7d04cbfc5

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
    [TopologicalSpace Θ] [T1Space Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    {m : ℕ} (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hpPos : ∀ j, 0 < p j) :
    (finiteProbabilityMeasure θ p hp : Measure Θ).support = range θ := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed (finite_range θ).isClosed
      (finiteProbabilityMeasure_ae_mem_range θ p hp)
  · rintro x ⟨j, rfl⟩
    apply (Measure.mem_support_iff_forall (θ j)).mpr
    intro U hU
    have hsub : {θ j} ⊆ U := singleton_subset_iff.mpr (mem_of_mem_nhds hU)
    have hsingle : 0 < (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} := by
      rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp]
      exact ENNReal.ofReal_pos.mpr (hpPos j)
    exact hsingle.trans_le (measure_mono hsub)
