-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:46.981012+00:00
-- url     : https://prove2.me/submissions/1ef04407-42c1-4a59-8f6f-0e9b5e4976c7

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
















/-- There is no zero-free three-element support in a group of order < 4. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
    (hn : Fintype.card G < 4) :
    maxObservedZeroFreeFibreSize (G := G) = 0 := by
  have hEveryTripleHitsZero (S : Finset G) (hS3 : S.card = 3) :
      (0 : G) ∈ S := by
    by_contra hZero
    have hSub : S ⊆ (Finset.univ : Finset G).erase (0 : G) := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      exact hZero (heq ▸ hx)
    have hc : ((Finset.univ : Finset G).erase (0 : G)).card =
        Fintype.card G - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : G))]
      simp
    have hBound := Finset.card_le_card hSub
    rw [hc, hS3] at hBound
    omega
  have hNone : (nonemptyFullFibres : Finset (Finset (Finset G))) = ∅ := by
    ext F
    constructor
    · intro hF
      obtain ⟨hAll, ⟨S, hS⟩⟩ := Finset.mem_filter.mp hF
      have hSIn : S ∈ F := (Finset.mem_filter.mp hS).1
      have hS3 : S.card = 3 := by
        have hSq : squareFibre S = F :=
          allSquareFibres_squareFibre_member F hAll S hSIn
        rw [← hSq] at hSIn
        exact ((mem_squareFibre S S).mp hSIn).1
      have hAvoid : (0 : G) ∉ S := (Finset.mem_filter.mp hS).2
      exact False.elim (hAvoid (hEveryTripleHitsZero S hS3))
    · intro hF
      simp at hF
  have hEmpty : (zeroFreeFullFibres : Finset (Finset (Finset G))) = ∅ := by
    simp [zeroFreeFullFibres, hNone]
  simp [maxObservedZeroFreeFibreSize, hEmpty]

























end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LT.lt.{0} Nat instLTNat (@Fintype.card.{p2m_u_0} G inst_2)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Eq.{1} Nat (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four

