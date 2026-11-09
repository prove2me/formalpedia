-- Prove2me | solution 1 for Couret.STROBO2TORS.squareDeltaGraph_edges_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:50.485973+00:00
-- url     : https://prove2.me/submissions/eee3b943-de95-48eb-b03d-c58692d9c07d

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









/-- The unordered edge count is the sum of the two disjoint branch counts. -/
theorem p2m_local_squareDeltaGraph_edges_partition (k : ℕ) :
    (squareDeltaGraph (G := G) k).edgeFinset.card =
      (ordinaryDeltaGraph (G := G) k).edgeFinset.card +
        (nontranslationDeltaGraph (G := G) k).edgeFinset.card := by
  classical
  have hSum :
      (∑ S : Finset G, (squareDeltaGraph (G := G) k).degree S) =
        (∑ S : Finset G, (ordinaryDeltaGraph (G := G) k).degree S) +
          (∑ S : Finset G, (nontranslationDeltaGraph (G := G) k).degree S) := by
    calc
      _ = ∑ S : Finset G, ((ordinaryDeltaGraph (G := G) k).degree S +
          (nontranslationDeltaGraph (G := G) k).degree S) := by
        apply Finset.sum_congr rfl
        intro S _
        exact squareDeltaGraph_degree S k
      _ = _ := Finset.sum_add_distrib
  rw [(squareDeltaGraph (G := G) k).sum_degrees_eq_twice_card_edges,
    (ordinaryDeltaGraph (G := G) k).sum_degrees_eq_twice_card_edges,
    (nontranslationDeltaGraph (G := G) k).sum_degrees_eq_twice_card_edges] at hSum
  omega
























end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
        (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
          (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
          (@Couret.STROBO2TORS.squareDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k))))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k)
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.nontranslationDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k))))) := @_root_.Couret.STROBO2TORS.p2m_local_squareDeltaGraph_edges_partition

