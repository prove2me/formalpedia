-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_edges_partition
-- name    : Couret.STROBO2TORS.squareDeltaGraph_edges_partition
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:43.03513+00:00
-- url     : https://prove2.me/theorems/57a6d7b0-425d-47f9-9a49-51d2580ccb0e
-- title:
--   Square-collision edges partition into ordinary and nontranslation edges
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For each $k\in\mathbb N$, let $e_k$, $o_k$, $n_k$ count unordered edges between distinct triples of equal ordered square and symmetric-difference size $k$, restricting respectively to all collisions, ordinary collisions, and nontranslation collisions. Then
--
--   $$e_k=o_k+n_k.$$
--
--   The layers may be empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 116–136; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.squareDeltaGraph_edges_partition

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_degree
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered pair counts at symmetric-difference sizes two, four and six.
The vertices are three-element subsets of a finite abelian group; zero is
permitted. The graph adjacency theorem identifies the counted objects with
the labelled ordered convolution square, including diagonal pairs.
The two branch graphs have disjoint neighbour sets, so their edge counts
add. Natural-number subtraction is used throughout, including small groups.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem squareDeltaGraph_edges_partition (k : ℕ) :
    (squareDeltaGraph (G := G) k).edgeFinset.card =
      (ordinaryDeltaGraph (G := G) k).edgeFinset.card +
        (nontranslationDeltaGraph (G := G) k).edgeFinset.card := by sorry

























end Couret.STROBO2TORS
