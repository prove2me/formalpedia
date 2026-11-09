-- Prove2me | solution 1 for Couret.STROBO2TORS.squareDeltaGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:50.852836+00:00
-- url     : https://prove2.me/submissions/7639d5f9-528c-4687-a0bf-3ac79930eda9

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





/-- The graph counts exactly the intended labelled ordered-square collisions. -/
theorem p2m_local_squareDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (squareDeltaGraph (G := G) k).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (S ∆ T).card = k := by
  change ((ordinaryDeltaGraph (G := G) k).Adj S T ∨
    (nontranslationDeltaGraph (G := G) k).Adj S T) ↔ _
  constructor
  · rintro (ho | he)
    · rcases ho with ⟨⟨hS, hT, hST, hOrd⟩, hdelta⟩
      exact ⟨hS, hT, hST, orderedSquare_eq_of_ordinaryPartner S T hS hOrd, hdelta⟩
    · rcases (nontranslationDeltaGraph_adj_iff S T k).mp he with
        ⟨hS, hT, hsq, hnot, hdelta⟩
      have hST : S ≠ T := by
        intro heq
        apply hnot
        exact ⟨0, by simpa [translateSupport] using heq.symm⟩
      exact ⟨hS, hT, hST, hsq, hdelta⟩
  · rintro ⟨hS, hT, hST, hsq, hdelta⟩
    rcases (orderedSquare_classification_iff S T hS hT).mp hsq with ho | he
    · exact Or.inl ⟨⟨hS, hT, hST, ho⟩, hdelta⟩
    · apply Or.inr
      exact (nontranslationDeltaGraph_adj_iff S T k).mpr
        ⟨hS, hT, hsq, exceptionalPartner_not_any_translation S T hS hT he, hdelta⟩




























end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S T : Finset.{p2m_u_0} G) (k : Nat),
  Iff
    (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S T)
    (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S T)
          (And
            (∀ (z : G),
              @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z))
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
              k))))) := @_root_.Couret.STROBO2TORS.p2m_local_squareDeltaGraph_adj_iff

