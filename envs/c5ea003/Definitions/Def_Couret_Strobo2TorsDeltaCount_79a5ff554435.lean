-- Prove2me | Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
-- name    : Couret_Strobo2TorsDeltaCount_79a5ff554435
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:31.281597+00:00
-- url     : https://prove2.me/theorems/f2e1867f-e8f4-4643-bd91-5edaa2593bd1
-- title:
--   Collision graphs at a prescribed symmetric-difference size
-- statement:
--   For a finite abelian group, the graph at distance $k$ has three-element supports as active vertices, with distinct $S,T$ adjacent when $$Q_S=Q_T,\qquad|S\triangle T|=k.$$ The pair-count definition is its finite number of edges, so unordered collision pairs are counted once.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsDeltaCount.lean; source file SHA-256 ef09c8cbd39579c9c01a7881f4d218e3fdcbd5e90916131e3bd3e7c80a42eb7e

import Aesop
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

/-- All equal-square collision edges at the prescribed delta, zero permitted. -/
def squareDeltaGraph (k : ℕ) : SimpleGraph (Finset G) :=
  ordinaryDeltaGraph k ⊔ nontranslationDeltaGraph k

noncomputable instance squareDeltaGraph_decidableRel (k : ℕ) :
    DecidableRel (squareDeltaGraph (G := G) k).Adj := Classical.decRel _



















/-- Number of unordered pairs of distinct triples with equal square and delta k. -/
noncomputable def squareDeltaPairCount (k : ℕ) : ℕ :=
  (squareDeltaGraph (G := G) k).edgeFinset.card










end Couret.STROBO2TORS


