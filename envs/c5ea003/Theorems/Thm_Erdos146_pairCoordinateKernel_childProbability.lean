-- Prove2me | Theorems.Thm_Erdos146_pairCoordinateKernel_childProbability
-- name    : Erdos146.pairCoordinateKernel_childProbability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:45:33.528981+00:00
-- url     : https://prove2.me/theorems/b9dc12c6-1a9d-4f4b-92f4-022c0ae3bf78
-- title:
--   The coordinate kernel reproduces the child probability
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. The kernel read off from a coordinate of the arrays assigns the child bit its empirical probability.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13424-L13437

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairCoordinateKernel_childProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    (pairCoordinateKernel hparents parents children coordinate).childProbability
        left right =
      ((pairTypeGroupChildOnes parents children coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
          ((pairTypeGroup parents coordinate
            (pairBitTypeOfOutcomes left right)).card : ℝ) := by sorry
