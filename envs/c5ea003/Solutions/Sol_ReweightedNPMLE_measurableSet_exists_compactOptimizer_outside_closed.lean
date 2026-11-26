-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_exists_compactOptimizer_outside_closed
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:47.848803+00:00
-- url     : https://prove2.me/submissions/b9d1d58c-97fb-46ed-9b65-5ecc6acb5cde

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_measurableSet_exists_compactOptimizer_strict_gap

-- Inline helpers preserved from ReweightedNPMLE.CompactOptimizerEvents.
section
/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

namespace ReweightedNPMLE



theorem isClosed_compactOptimizerGraph {X M : Type*}
    [TopologicalSpace X] [TopologicalSpace M] (U : X × M → ℝ) (hU : Continuous U) :
    IsClosed (compactOptimizerGraph U) := by
  have heq : compactOptimizerGraph U = ⋂ μ : M, {p | U (p.1, μ) ≤ U p} := by
    ext p
    constructor
    · intro hp
      exact mem_iInter.mpr (fun μ ↦ hp.2 μ (mem_univ μ))
    · intro hp
      exact ⟨mem_univ p.2, fun μ _ ↦ mem_iInter.mp hp μ⟩
  rw [heq]
  exact isClosed_iInter (fun μ ↦ isClosed_le
    (hU.comp (continuous_fst.prodMk continuous_const)) hU)











end ReweightedNPMLE
end

/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Existence of an optimizing law outside any fixed closed law set is
Borel. Applied to the compact at-most-`m`-atom laws, this measures support
failure without assuming finite support of arbitrary optimizers. -/
theorem solution {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) (F : Set M) (hF : IsClosed F) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} := by
  by_cases hne : F.Nonempty
  · have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} =
        {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < Metric.infDist μ F} := by
      ext x
      simp only [mem_setOf_eq, hF.notMem_iff_infDist_pos hne]
    rw [heq]
    exact measurableSet_exists_compactOptimizer_strict_gap U
      (fun p ↦ Metric.infDist p.2 F) hU ((Metric.continuous_infDist_pt F).comp continuous_snd)
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hne
    have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} =
        Prod.fst '' compactOptimizerGraph U := by
      ext x
      simp only [hFempty, mem_empty_iff_false, not_false_eq_true, and_true,
        mem_setOf_eq, mem_image]
      constructor
      · rintro ⟨μ, hμ⟩
        exact ⟨(x, μ), hμ, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.2, hp⟩
    rw [heq]
    exact (isClosedMap_fst_of_compactSpace _ (isClosed_compactOptimizerGraph U hU)).measurableSet
