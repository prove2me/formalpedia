-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_compactOptimizer_nonunique
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:04.54044+00:00
-- url     : https://prove2.me/submissions/56457f90-b4c0-4e5e-8a04-2545242a90d7

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
theorem solution {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) :
    MeasurableSet {x | ∃ μ ν : M, (x, μ) ∈ compactOptimizerGraph U ∧
      (x, ν) ∈ compactOptimizerGraph U ∧ μ ≠ ν} := by
  let S := fun j : ℕ ↦ {p : X × (M × M) |
    (p.1, p.2.1) ∈ compactOptimizerGraph U ∧
    (p.1, p.2.2) ∈ compactOptimizerGraph U ∧
    1 ≤ ((j : ℝ) + 1) * dist p.2.1 p.2.2}
  have hS : ∀ j, IsClosed (S j) := by
    intro j
    exact ((isClosed_compactOptimizerGraph U hU).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
      (((isClosed_compactOptimizerGraph U hU).preimage
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).inter
        (isClosed_le continuous_const (continuous_const.mul
          ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd)))))
  have heq : {x | ∃ μ ν : M, (x, μ) ∈ compactOptimizerGraph U ∧
      (x, ν) ∈ compactOptimizerGraph U ∧ μ ≠ ν} = ⋃ j : ℕ, Prod.fst '' S j := by
    ext x
    constructor
    · rintro ⟨μ, ν, hμ, hν, hneq⟩
      obtain ⟨j, hj⟩ := positive_iff_exists_nat_mul_ge_one.mp (dist_pos.mpr hneq)
      exact mem_iUnion.mpr ⟨j, ⟨(x, μ, ν), ⟨hμ, hν, hj⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, p, hp, rfl⟩ := mem_iUnion.mp hx
      refine ⟨p.2.1, p.2.2, hp.1, hp.2.1, ?_⟩
      exact dist_pos.mp (positive_iff_exists_nat_mul_ge_one.mpr ⟨j, hp.2.2⟩)
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ (isClosedMap_fst_of_compactSpace _ (hS j)).measurableSet)
