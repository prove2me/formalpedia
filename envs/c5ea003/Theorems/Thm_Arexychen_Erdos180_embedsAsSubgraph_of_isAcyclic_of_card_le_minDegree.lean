-- Prove2me | Theorems.Thm_Arexychen_Erdos180_embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
-- name    : Arexychen.Erdos180.embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:19.192985+00:00
-- url     : https://prove2.me/theorems/6c500fa0-d8ef-4128-899c-2871a54d8f57
-- title:
--   Embedding a finite forest under cardinality and minimum-degree bounds
-- statement:
--   Let $F$ and $G$ be simple graphs on finite vertex types $\alpha$ and $\beta$, respectively, and assume that adjacency in $G$ is decidable. If $F$ is acyclic and $|\alpha|\le |\beta|$ and $|\alpha|\le\delta(G)$, then there exists an injective map $\alpha\to\beta$ preserving every edge of $F$. This is ordinary subgraph containment: nonedges need not be preserved. Both cardinality bounds are retained, and the vertex count of $F$ includes isolated vertices.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L221-L230

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

theorem Arexychen.Erdos180.embedsAsSubgraph_of_isAcyclic_of_card_le_minDegree
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (F : SimpleGraph α) (G : SimpleGraph β)
    [DecidableRel G.Adj]
    (hF : F.IsAcyclic)
    (hcard : Fintype.card α ≤ Fintype.card β)
    (hdeg : Fintype.card α ≤ G.minDegree) :
    EmbedsAsSubgraph F G := by sorry
