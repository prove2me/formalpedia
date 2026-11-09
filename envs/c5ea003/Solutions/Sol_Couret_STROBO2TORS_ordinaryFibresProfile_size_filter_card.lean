-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibresProfile_size_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:30.950349+00:00
-- url     : https://prove2.me/submissions/9504edb4-82e9-44f3-af25-c1d85a67f2ee

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_zeroFree_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





/-- Within one ordinary profile the size after deleting zero is constant,
so the filtered profile contributes either its entire cardinality or zero. -/
theorem p2m_local_ordinaryFibresProfile_size_filter_card (j k : ℕ) :
    ((ordinaryFibresProfile (G := G) j).filter
      (fun F => (withoutZero F).card = k)).card =
      if (twoTorsion : Finset G).card - j = k then
        (ordinaryFibresProfile (G := G) j).card else 0 := by
  by_cases hk : (twoTorsion : Finset G).card - j = k
  · rw [if_pos hk]
    have heq : ((ordinaryFibresProfile (G := G) j).filter
        (fun F => (withoutZero F).card = k)) =
        ordinaryFibresProfile j := by
      ext F
      constructor
      · exact fun h => (Finset.mem_filter.mp h).1
      · intro hF
        exact Finset.mem_filter.mpr
          ⟨hF, (ordinaryFibresProfile_zeroFree_card j F hF).trans hk⟩
    rw [heq]
  · rw [if_neg hk]
    have heq : ((ordinaryFibresProfile (G := G) j).filter
        (fun F => (withoutZero F).card = k)) = ∅ := by
      ext F
      constructor
      · intro hF
        obtain ⟨hProf, hSize⟩ := Finset.mem_filter.mp hF
        exact False.elim
          (hk ((ordinaryFibresProfile_zeroFree_card j F hProf).symm.trans hSize))
      · intro hEmpty
        simp at hEmpty
    rw [heq, Finset.card_empty]







end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j k : Nat),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun F =>
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F)) k)
        (fun a =>
          instDecidableEqNat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a)) k)
        (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j)))
    (@ite.{1} Nat
      (@Eq.{1} Nat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) j)
        k)
      (instDecidableEqNat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) j)
        k)
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibresProfile_size_filter_card

