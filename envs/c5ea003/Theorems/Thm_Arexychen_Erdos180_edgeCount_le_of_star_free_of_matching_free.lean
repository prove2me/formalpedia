-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_le_of_star_free_of_matching_free
-- name    : Arexychen.Erdos180.edgeCount_le_of_star_free_of_matching_free
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:45.673611+00:00
-- url     : https://prove2.me/theorems/4d4fb280-ff85-452b-9bac-9207f712fa48
-- title:
--   A constant edge bound from excluding a star and a matching
-- statement:
--   Let $a,b,n$ be natural numbers with $a\ge2$ and $b\ge2$. If a simple graph $G$ on $\operatorname{Fin}(n)$ has decidable adjacency and contains neither the star $K_{1,a}$ nor the $b$-edge matching $bK_2$ as an ordinary subgraph, then
--
--   $$e(G)\le 2(a-1)(b-1).$$
--
--   This is the existing vertex-cover bound used in the forest/linear classification related to Erdős Problem #180; no optimality or mathematical novelty is claimed.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/ExplicitConstant.lean#L124-L142

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

theorem Arexychen.Erdos180.edgeCount_le_of_star_free_of_matching_free
    {n a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hstar : IsHFree (starGraph (0 : Fin (a + 1))) G)
    (hmatch : IsHFree (matchingGraph b) G) :
    edgeCount G ≤ 2 * (a - 1) * (b - 1) := by sorry
