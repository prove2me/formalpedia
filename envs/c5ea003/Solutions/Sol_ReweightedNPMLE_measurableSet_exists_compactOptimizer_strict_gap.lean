-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_exists_compactOptimizer_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:06.270817+00:00
-- url     : https://prove2.me/submissions/b2e5c5d6-3b1a-4440-9a8e-6d712dcbd787

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
import Theorems.Thm_ReweightedNPMLE_positive_iff_exists_nat_mul_ge_one

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
/-- Strict inequalities for some optimizing law are Borel, even though the
optimizing law itself has not been chosen measurably. -/
theorem solution {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (U V : X × M → ℝ) (hU : Continuous U) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < V (x, μ)} := by
  let S := fun j : ℕ ↦ compactOptimizerGraph U ∩ {p | 1 ≤ ((j : ℝ) + 1) * V p}
  have hS : ∀ j, IsClosed (S j) := fun j ↦
    (isClosed_compactOptimizerGraph U hU).inter
      (isClosed_le continuous_const (continuous_const.mul hV))
  have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < V (x, μ)} =
      ⋃ j : ℕ, Prod.fst '' S j := by
    ext x
    constructor
    · rintro ⟨μ, hμ, hVμ⟩
      obtain ⟨j, hj⟩ := positive_iff_exists_nat_mul_ge_one.mp hVμ
      exact mem_iUnion.mpr ⟨j, ⟨(x, μ), ⟨hμ, hj⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, p, hp, rfl⟩ := mem_iUnion.mp hx
      exact ⟨p.2, hp.1, positive_iff_exists_nat_mul_ge_one.mpr ⟨j, hp.2⟩⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ (isClosedMap_fst_of_compactSpace _ (hS j)).measurableSet)
