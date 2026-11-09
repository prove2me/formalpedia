-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
-- name    : Couret.STROBO2TORS.squareDeltaGraph_adj_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:48.244643+00:00
-- url     : https://prove2.me/theorems/cfb86b86-235a-475c-b156-c4f4acd3fd0c
-- title:
--   Adjacency in the square-collision distance graph
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For supports $S,T$ and natural $k$, $$S\sim_{\Gamma_k}T\iff |S|=|T|=3,\ S\ne T,\ Q_S=Q_T,\ |S\triangle T|=k.$$
--
--   This explicitly retains inequality even at distance zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 64–88; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.squareDeltaGraph_adj_iff

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
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

theorem squareDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (squareDeltaGraph (G := G) k).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (S ∆ T).card = k := by sorry





























end Couret.STROBO2TORS
