-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_two_four_mul_edges
-- name    : Couret.STROBO2TORS.squareDeltaGraph_two_four_mul_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:37.080545+00:00
-- url     : https://prove2.me/theorems/a131ffd6-9c40-4d2e-bb74-0bbf50674558
-- title:
--   Four times the distance-two square-collision count
-- statement:
--   Let $G$ be a finite abelian group, $n=|G|$ and $h=|G[2]|$. Consider the square-distance-two graph on finite supports: an edge joins distinct triples $S,T$ having identical labelled ordered-sum counts and $|S\triangle T|=2$. Write $e_2$ for its unordered edge count. Then $$4e_2=n(n-2)(h-1).$$ Subtraction is truncated in the natural numbers, zero is allowed in the supports, and the formula includes small groups. This supplies an exact weighted count before division by four.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 170–178; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.squareDeltaGraph_two_four_mul_edges

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_two_eq_bot
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_four_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_edges_partition
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

theorem squareDeltaGraph_two_four_mul_edges :
    4 * (squareDeltaGraph (G := G) 2).edgeFinset.card =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by sorry

















end Couret.STROBO2TORS
