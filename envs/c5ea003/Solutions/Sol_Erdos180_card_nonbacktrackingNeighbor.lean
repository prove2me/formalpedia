-- Prove2me | solution 1 for Erdos180.card_nonbacktrackingNeighbor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:52:02.666198+00:00
-- url     : https://prove2.me/submissions/15ef0f81-9bf8-4e5a-802c-54d26e52d6a8

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite

open Erdos180
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by
  classical
  calc
    Fintype.card (NonbacktrackingNeighbor G previous current) =
        ((G.neighborFinset current).erase previous).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext next
      simp [and_comm]
    _ = G.degree current - 1 := by
      rw [Finset.card_erase_of_mem]
      · rfl
      · simpa using hedge
