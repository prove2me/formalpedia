-- Prove2me | solution 1 for Couret.STROBO2TORS.squareDeltaGraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:45.087425+00:00
-- url     : https://prove2.me/submissions/56a8294c-d6bf-4732-8fce-5df0f3ec206c

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







/-- The ordinary and nontranslation branches contribute disjoint neighbours. -/
theorem p2m_local_squareDeltaGraph_degree (S : Finset G) (k : ℕ) :
    (squareDeltaGraph (G := G) k).degree S =
      (ordinaryDeltaGraph (G := G) k).degree S +
        (nontranslationDeltaGraph (G := G) k).degree S := by
  classical
  have hNeighbours :
      (squareDeltaGraph (G := G) k).neighborFinset S =
        (ordinaryDeltaGraph (G := G) k).neighborFinset S ∪
          (nontranslationDeltaGraph (G := G) k).neighborFinset S := by
    ext T
    simp [squareDeltaGraph]
  have hDisjoint :
      Disjoint ((ordinaryDeltaGraph (G := G) k).neighborFinset S)
        ((nontranslationDeltaGraph (G := G) k).neighborFinset S) := by
    apply Finset.disjoint_left.mpr
    intro T ho he
    have hOrd : (ordinaryDeltaGraph (G := G) k).Adj S T := by simpa using ho
    have hExc : (nontranslationDeltaGraph (G := G) k).Adj S T := by simpa using he
    rcases hOrd with ⟨⟨_, _, _, u, _, hTu⟩, _⟩
    exact ((nontranslationDeltaGraph_adj_iff S T k).mp hExc).2.2.2.1 ⟨u, hTu⟩
  change ((squareDeltaGraph (G := G) k).neighborFinset S).card =
    ((ordinaryDeltaGraph (G := G) k).neighborFinset S).card +
      ((nontranslationDeltaGraph (G := G) k).neighborFinset S).card
  rw [hNeighbours, Finset.card_union_of_disjoint hDisjoint]


























end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G) (k : Nat),
  @Eq.{1} Nat
    (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
      (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S))
        (fun a =>
          @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
            (@Couret.STROBO2TORS.squareDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k) a)
        (@Finset.fintype.{p2m_u_0} G inst_2)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
        (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S))
          (fun a =>
            @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
              (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k) a)
          (@Finset.fintype.{p2m_u_0} G inst_2)))
      (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
        (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S))
          (fun a =>
            @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S
              (@Couret.STROBO2TORS.nontranslationDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2 k) a)
          (@Finset.fintype.{p2m_u_0} G inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_squareDeltaGraph_degree

