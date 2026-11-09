-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_two_eq_bot
-- name    : Couret.STROBO2TORS.nontranslationDeltaGraph_two_eq_bot
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:47.143528+00:00
-- url     : https://prove2.me/theorems/5d5deafc-cddc-45c6-a2d0-6d94643675aa
-- title:
--   The nontranslation collision graph at symmetric difference two is empty
-- statement:
--   For every finite abelian additive group G with decidable equality, the simple graph nontranslationDeltaGraph 2 on all finite subsets of G is the bottom graph, with no edges. Its possible edges would join three-element supports S,T having the same labelled ordered-square function, symmetric difference of cardinality two, and no ambient translation carrying S to T. Non-triple vertices are isolated, and zero is allowed in either support. The statement also includes groups too small to have a three-element support.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean, lines 138–150; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e; theorem Couret.STROBO2TORS.nontranslationDeltaGraph_two_eq_bot

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
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
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

theorem nontranslationDeltaGraph_two_eq_bot :
    nontranslationDeltaGraph (G := G) 2 = ⊥ := by sorry























end Couret.STROBO2TORS
