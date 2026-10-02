-- Prove2me | Theorems.Thm_Arexychen_Erdos180_embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
-- name    : Arexychen.Erdos180.embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:51.819284+00:00
-- url     : https://prove2.me/theorems/4bdac033-462b-48cc-9456-34718d5e5809
-- title:
--   Embedding a graph with matching reduction into a canonical matching
-- statement:
--   Let $H$ be a simple graph on a finite vertex type $\alpha$. If, after deleting isolated vertices, each vertex has at most one neighbor, then the whole $H$ embeds as an ordinary subgraph into the canonical matching with $|\alpha|$ edges. The target has vertex type $\operatorname{Fin}(|\alpha|)\times\mathrm{Bool}$; isolated vertices of $H$ are retained.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Matching.lean#L108-L226

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hmatch : IsMatchingGraph (deleteIsolated H)) :
    EmbedsAsSubgraph H (matchingGraph (Fintype.card α)) := by sorry
