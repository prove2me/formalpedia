-- Prove2me | Theorems.Thm_Arexychen_Erdos180_matching_embedding_of_edgeFinset_card_ge
-- name    : Arexychen.Erdos180.matching_embedding_of_edgeFinset_card_ge
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:50.617901+00:00
-- url     : https://prove2.me/theorems/266aae8e-c5ec-4ff5-b03d-a41b3446e7f2
-- title:
--   Embedding a canonical matching from a finite matching subgraph
-- statement:
--   Let $M$ be a matching subgraph of a simple graph $G$ on an arbitrary vertex type. Assume decidable adjacency for $M$ and a finite enumeration of its vertices. If the graph on those vertices has at least $b$ unordered edges, then the canonical $b$-edge matching on $\operatorname{Fin}(b)\times\mathrm{Bool}$ embeds into $G$ by an injective edge-preserving map. The natural number $b$ may be zero, and the ambient vertex type need not be finite.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/MatchingEdgeFinset.lean#L12-L127

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

theorem Arexychen.Erdos180.matching_embedding_of_edgeFinset_card_ge
    {V : Type u} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) [DecidableRel M.Adj] [Fintype M.verts]
    {b : ℕ} (hcard : b ≤ M.coe.edgeFinset.card) :
    EmbedsAsSubgraph (matchingGraph b) G := by sorry
