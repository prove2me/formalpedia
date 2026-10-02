-- Prove2me | Theorems.Thm_Arexychen_Erdos180_embeds_of_deleteIsolated_isStar_of_degree_ge_card
-- name    : Arexychen.Erdos180.embeds_of_deleteIsolated_isStar_of_degree_ge_card
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:48.687103+00:00
-- url     : https://prove2.me/theorems/c77618fa-253a-48f0-a5d8-9e40ae5745aa
-- title:
--   Embedding a reduced star while accommodating isolated vertices
-- statement:
--   Let $H$ be a graph on a finite vertex type $\alpha$, let $G$ be a graph on any vertex type, and let $v$ be a vertex of $G$ with a finite neighbor set. If deleting isolated vertices from $H$ leaves a star and $|\alpha|\le\deg_G(v)$, then the whole graph $H$ admits an injective edge-preserving map into $G$. Its isolated vertices are included in the bound $|\alpha|$.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Upper.lean#L12-L84

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

theorem Arexychen.Erdos180.embeds_of_deleteIsolated_isStar_of_degree_ge_card
    {α : Type u} {β : Type v} [Fintype α]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : β)
    [Fintype (G.neighborSet v)]
    (hstar : IsStar (deleteIsolated H))
    (hdeg : Fintype.card α ≤ G.degree v) :
    EmbedsAsSubgraph H G := by sorry
