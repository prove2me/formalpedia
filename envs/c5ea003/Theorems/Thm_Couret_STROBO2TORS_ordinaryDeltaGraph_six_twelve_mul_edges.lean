-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_six_twelve_mul_edges
-- name    : Couret.STROBO2TORS.ordinaryDeltaGraph_six_twelve_mul_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:42.114201+00:00
-- url     : https://prove2.me/theorems/82edf0d0-f6b3-4830-aeee-9f34f67f3cad
-- title:
--   Twelve times the ordinary disjoint collision count
-- statement:
--   Let $G$ be a finite abelian group, $n=|G|$, and $h=|G[2]|$, where $G[2]=\{u:2u=0\}$. The ordinary distance-six graph has finite supports as vertices and edges between distinct three-element supports $S,T$ related by $T=S+u$ for some $u\in G[2]$, with $|S\triangle T|=6$. Thus its active endpoints are disjoint triples. Its unordered edge count $e_6^{\mathrm{ord}}$ satisfies $$12e_6^{\mathrm{ord}}=n(n-2)(n-4)(h-1).$$ Every subtraction is natural truncated subtraction; zero is permitted in supports and no size bound on $G$ is imposed. This weighted identity certifies exact divisibility of the numerator by twelve.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 152–161; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.ordinaryDeltaGraph_six_twelve_mul_edges

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_four_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_six_twice_edges
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

theorem ordinaryDeltaGraph_six_twelve_mul_edges :
    12 * (ordinaryDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * (Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1) := by sorry





















end Couret.STROBO2TORS
