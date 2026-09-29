-- Prove2me | solution 1 for Erdos146.pairTypeGroup_true_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:17:45.182626+00:00
-- url     : https://prove2.me/submissions/1012028f-9620-4e06-9f3e-391006ffbea2

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Theorems.Thm_Erdos146_pairParentCoordinateSupport_true_card
import Theorems.Thm_Erdos146_pairTypeGroup_homogeneous_card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_true_card] using
    pairTypeGroup_homogeneous_card parents coordinate true
