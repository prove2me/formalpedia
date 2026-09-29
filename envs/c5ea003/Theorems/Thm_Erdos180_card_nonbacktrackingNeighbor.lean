-- Prove2me | Theorems.Thm_Erdos180_card_nonbacktrackingNeighbor
-- name    : Erdos180.card_nonbacktrackingNeighbor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:10:00.956698+00:00
-- url     : https://prove2.me/theorems/79769693-d6de-4415-8529-cceb3fa5f54b
-- title:
--   Choices for the next step of a non-backtracking walk
-- statement:
--   If $G$ has an edge from the current vertex to the previous one, the number of ways to
--   continue a non-backtracking walk is
--
--   $$\deg_G(\text{current}) - 1.$$
--
--   Iterating this from a vertex of degree at least $d$ produces the $d(d-1)^3$ non-backtracking
--   four-edge walks counted in Lemma 3.2 of the source.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L3175-L3191

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite

open Erdos180
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Erdos180.card_nonbacktrackingNeighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by sorry
