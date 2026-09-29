-- Prove2me | Theorems.Thm_Erdos146_pairTypeGroup_homogeneous_card
-- name    : Erdos146.pairTypeGroup_homogeneous_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:44:54.297435+00:00
-- url     : https://prove2.me/theorems/dd180c80-37ab-49f5-aaff-870c88a8e9bd
-- title:
--   Size of a homogeneous type group
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. Cardinality of a type group all of whose coordinates agree.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13294-L13316

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairTypeGroup_homogeneous_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 := by sorry
