-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
-- name    : Arexychen.Erdos180.edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:37.269986+00:00
-- url     : https://prove2.me/theorems/42a8a1bd-3e33-471e-a030-b7fe8a25dc80
-- title:
--   An edge-covering vertex set bounds the number of edges
-- statement:
--   Let $G$ be a simple graph on a finite vertex type, with decidable adjacency. Let $T$ be a finite set of vertices and let $A$ be a natural number. If every vertex in $T$ has degree at most $A$, and every edge has at least one endpoint in $T$, then
--
--   $$e(G)\le |T|A.$$
--
--   No degree restriction is imposed outside $T$.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Bounds.lean#L12-L47

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
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (A : ℕ)
    (hdeg : ∀ v ∈ T, G.degree v ≤ A)
    (hcover : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ T ∨ y ∈ T) :
    edgeCount G ≤ T.card * A := by sorry
