-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic
-- name    : Arexychen.Erdos180.edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:35.564974+00:00
-- url     : https://prove2.me/theorems/fa538b0e-602e-4e4d-9e3c-1c1851f3cefa
-- title:
--   A uniform linear edge bound for a forbidden reduced forest
-- statement:
--   Fix a finite simple graph $H$. If the graph induced by its non-isolated vertices is acyclic, there is a natural number $C$ such that every finite simple graph $G$ with decidable adjacency satisfies
--
--   $$H\text{-free}(G)\;\Longrightarrow\;e(G)\le C\,|V(G)|.$$
--
--   The constant is chosen before the host vertex type and host graph. Freeness forbids an injective edge-preserving copy of the whole original graph $H$, including its isolated vertices.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L358-L369

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180

theorem Arexychen.Erdos180.edgeCount_le_of_isHFree_of_deleteIsolated_isAcyclic
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    ∃ C : ℕ, ∀ (β : Type v) [Fintype β] (G : SimpleGraph β)
      [DecidableRel G.Adj],
      IsHFree H G → edgeCount G ≤ C * Fintype.card β := by sorry
