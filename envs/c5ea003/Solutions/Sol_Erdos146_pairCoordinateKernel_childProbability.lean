-- Prove2me | solution 1 for Erdos146.pairCoordinateKernel_childProbability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:18:26.793332+00:00
-- url     : https://prove2.me/submissions/5f66ea0b-9334-4051-a933-a6f858cea6ad

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
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
            (pairBitTypeOfOutcomes left right)).card : ℝ) := by
  rfl
