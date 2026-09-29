-- Prove2me | Theorems.Thm_Erdos146_ParentSystem_graph_adj_iff
-- name    : Erdos146.ParentSystem.graph_adj_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:43:53.730539+00:00
-- url     : https://prove2.me/theorems/3b9c34b0-3bfd-42a2-a268-b686d481e4e3
-- title:
--   Adjacency in a parent system
-- statement:
--   Characterisation of adjacency in the abstract *parent system* that the layered graph of Section 6 instantiates: two vertices are adjacent exactly when one is a parent of the other.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11942-L11945

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos146
open Erdos146.ParentSystem
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.ParentSystem.graph_adj_iff {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by sorry
