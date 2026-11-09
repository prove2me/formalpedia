-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareDeltaPairCount_numeric
-- name    : Couret.STROBO2TORS.squareDeltaPairCount_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:42.689574+00:00
-- url     : https://prove2.me/theorems/4365e48d-ee2d-4143-a37a-629c404c75ae
-- title:
--   Exact collision counts at three distances
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. Let $C_k$ be the defined number of unordered square-collision pairs at symmetric-difference size $k$. Then $$C_2=n(n-2)(h-1)/4,\quad C_4=n(h-1)(t-1)/2,$$ and $$C_6=n(n-2)(n-4)(h-1)/12+n(h-1)^2(t-1)/2.$$ All expressions use natural-number subtraction and division, with no lower bound on $n$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 240–250; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.squareDeltaPairCount_numeric

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_six_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_six_twelve_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_edges_partition
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_two_four_mul_edges
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

theorem squareDeltaPairCount_numeric :
    let n := Fintype.card G
    let h := (twoTorsion : Finset G).card
    let t := (threeTorsion : Finset G).card
    squareDeltaPairCount (G := G) 2 = n * (n - 2) * (h - 1) / 4 ∧
    squareDeltaPairCount (G := G) 4 = n * (h - 1) * (t - 1) / 2 ∧
    squareDeltaPairCount (G := G) 6 =
      n * (n - 2) * (n - 4) * (h - 1) / 12 +
        n * (h - 1) ^ 2 * (t - 1) / 2 := by sorry



end Couret.STROBO2TORS
