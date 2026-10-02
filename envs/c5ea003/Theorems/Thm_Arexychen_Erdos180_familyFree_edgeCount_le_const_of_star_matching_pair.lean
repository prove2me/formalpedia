-- Prove2me | Theorems.Thm_Arexychen_Erdos180_familyFree_edgeCount_le_const_of_star_matching_pair
-- name    : Arexychen.Erdos180.familyFree_edgeCount_le_const_of_star_matching_pair
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:56.068786+00:00
-- url     : https://prove2.me/theorems/203e5dfe-6911-4adf-b6fd-2b98c29e602a
-- title:
--   A star–matching pair gives a uniform constant family edge bound
-- statement:
--   Let $F$ be a family of finite simple graphs indexed by a finite nonempty type. Suppose the family contains a member whose reduced graph is a star with at least two edges and a member whose reduced graph is a matching with at least two edges. There is a natural number $C$ such that every $F$-free graph on $\operatorname{Fin}(n)$ has at most $C$ edges, uniformly for all natural $n$. No forest condition is imposed on the other members.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Upper.lean#L218-L248

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
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

theorem Arexychen.Erdos180.familyFree_edgeCount_le_const_of_star_matching_pair
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hpair : FamilyContainsStarMatchingPair F) :
    ∃ C : ℕ, ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C := by sorry
