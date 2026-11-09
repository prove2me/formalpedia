-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_four_twice_edges_numeric
-- name    : Couret.STROBO2TORS.squareDeltaGraph_four_twice_edges_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:39.230256+00:00
-- url     : https://prove2.me/theorems/caf8e2e4-3a3e-456b-bcd8-cc587592fa99
-- title:
--   Exact unordered collision count at difference size four
-- statement:
--   Let G be a finite additive commutative group with decidable equality. Consider the simple graph on finite supports whose edges connect distinct three-element supports with the same labelled ordered additive convolution square and symmetric difference of cardinality four; both ordinary two-torsion-translation and nontranslation branches are included. Then twice its unordered edge count equals |G|·(|G[2]|−1)·(|G[3]|−1), in ℕ, where G[2]={u:u+u=0} and G[3]={v:v+v+v=0}. The subtractions are natural-number subtractions. Supports may contain zero; no lower bound on |G| or nontriviality of either torsion subgroup is assumed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 180–188; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.squareDeltaGraph_four_twice_edges_numeric

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_four_eq_bot
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

theorem squareDeltaGraph_four_twice_edges_numeric :
    2 * (squareDeltaGraph (G := G) 4).edgeFinset.card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by sorry















end Couret.STROBO2TORS
