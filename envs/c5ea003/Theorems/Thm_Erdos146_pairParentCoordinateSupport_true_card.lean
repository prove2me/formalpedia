-- Prove2me | Theorems.Thm_Erdos146_pairParentCoordinateSupport_true_card
-- name    : Erdos146.pairParentCoordinateSupport_true_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:44:42.112549+00:00
-- url     : https://prove2.me/theorems/c546706b-9a48-4c8d-a674-5cff2dea9b77
-- title:
--   Support size of a parent coordinate
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. The number of parent-array entries taking value $1$ in a given coordinate.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13198-L13204

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairParentCoordinateSupport_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by sorry
