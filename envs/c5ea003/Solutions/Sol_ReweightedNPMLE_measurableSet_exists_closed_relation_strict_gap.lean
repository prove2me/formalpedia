-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_exists_closed_relation_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:14:35.405802+00:00
-- url     : https://prove2.me/submissions/c893e63b-0c0c-4d5a-9569-1e63b95473da

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
/-- Strict gaps on any closed compact-law relation are Borel after
projection. In particular, two different optimization constraints can be
imposed on a pair of laws before testing an ordinary likelihood gap. -/
theorem solution {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (R : Set (X × M)) (hR : IsClosed R)
    (V : X × M → ℝ) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ R ∧ 0 < V (x, μ)} := by
  let S := fun j : ℕ ↦ R ∩ {p | 1 ≤ ((j : ℝ) + 1) * V p}
  have hS : ∀ j, IsClosed (S j) := fun j ↦
    hR.inter (isClosed_le continuous_const (continuous_const.mul hV))
  have heq : {x | ∃ μ : M, (x, μ) ∈ R ∧ 0 < V (x, μ)} =
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
