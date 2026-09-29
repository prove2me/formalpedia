-- Prove2me | solution 1 for Erdos146.pairCoordinatePairMismatchCount_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:20:41.631411+00:00
-- url     : https://prove2.me/submissions/4c170e1e-d55e-4a0d-8e88-66c4f26d937a

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool)
    (hgroup :
      pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0)) :
    pairCoordinatePairMismatchCount parents children coordinate pair =
      if children pair coordinate = outcome then 0 else 2 := by
  classical
  have hhomogeneous :=
    (pairCoordinateBitType_homogeneous_iff
      parents coordinate pair outcome).mp hgroup
  by_cases hchild : children pair coordinate = outcome
  · have hempty :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro parent hmember hdisagree
      exact hdisagree
        ((hhomogeneous parent hmember).trans hchild.symm)
    unfold pairCoordinatePairMismatchCount
    rw [hempty]
    simp [hchild]
  · have hfull :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) =
          pair.val := by
      ext parent
      constructor
      · intro hmember
        exact (Finset.mem_filter.mp hmember).1
      · intro hmember
        apply Finset.mem_filter.mpr
        refine ⟨hmember, ?_⟩
        intro hequal
        apply hchild
        exact hequal.symm.trans
          (hhomogeneous parent hmember)
    unfold pairCoordinatePairMismatchCount
    rw [hfull, if_neg hchild]
    exact pair.property
