-- Prove2me | Theorems.Thm_Erdos146_pairTypeGroup_true_card
-- name    : Erdos146.pairTypeGroup_true_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:45:21.023787+00:00
-- url     : https://prove2.me/theorems/59e674a1-ac49-4e98-9c53-ca0d2d4e29d2
-- title:
--   Size of the true-valued type group
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. Cardinality of the group of coordinates whose parent pair has the given type and child bit $1$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13327-L13334

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairTypeGroup_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by sorry
