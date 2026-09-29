-- Prove2me | Theorems.Thm_Erdos180_subdivisionGraph_base_pair_adj
-- name    : Erdos180.subdivisionGraph_base_pair_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:05:40.614341+00:00
-- url     : https://prove2.me/theorems/b651a6ea-501b-4b2d-b2e9-43290f877cac
-- title:
--   Bases are adjacent to their subdivision vertices
-- statement:
--   In $S_k$, the base vertex indexed by $b$ is adjacent to the subdivision vertex indexed by
--   the pair $(b, c)$, for every centre $c$.
--
--   $S_k$ is obtained from $K_{3,k}$ by replacing each edge with a two-edge path (Definition 2.1);
--   the subdivision vertex $(b,c)$ is the vertex inserted into the edge from base $b$ to centre
--   $c$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1855-L1860

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionGraph_base_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inl base)) (.inr (base, center)) := by sorry
