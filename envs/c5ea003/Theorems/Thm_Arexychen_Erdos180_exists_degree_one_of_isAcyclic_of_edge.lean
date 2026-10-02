-- Prove2me | Theorems.Thm_Arexychen_Erdos180_exists_degree_one_of_isAcyclic_of_edge
-- name    : Arexychen.Erdos180.exists_degree_one_of_isAcyclic_of_edge
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:15.205152+00:00
-- url     : https://prove2.me/theorems/25c2e0e9-3388-48ce-9927-c023b6494818
-- title:
--   A finite forest with an edge has a vertex of degree one
-- statement:
--   Let $F$ be a simple graph on a finite vertex type, with decidable adjacency. If $F$ is acyclic and its finite edge set is nonempty, then some vertex has degree exactly one.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L56-L84

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

theorem Arexychen.Erdos180.exists_degree_one_of_isAcyclic_of_edge
    {α : Type u} [Fintype α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hF : F.IsAcyclic) (hedge : F.edgeFinset.Nonempty) :
    ∃ v : α, F.degree v = 1 := by sorry
