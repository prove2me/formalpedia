-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalParams_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:30.371167+00:00
-- url     : https://prove2.me/submissions/dc95f1b4-da97-4ccf-a0be-8774746b149b

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]















theorem p2m_local_exceptionalParams_card :
    (exceptionalParams : Finset ((G × G) × G)).card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by
  have h0H : (0 : G) ∈ twoTorsion := (mem_twoTorsion 0).mpr (by simp)
  have h0K : (0 : G) ∈ threeTorsion := (mem_threeTorsion 0).mpr (by simp)
  unfold exceptionalParams
  calc
    (((Finset.univ : Finset G).product ((twoTorsion : Finset G).erase 0)).product
        ((threeTorsion : Finset G).erase 0)).card =
        ((Finset.univ : Finset G).product ((twoTorsion : Finset G).erase 0)).card *
          ((threeTorsion : Finset G).erase 0).card :=
      Finset.card_product ((Finset.univ : Finset G).product ((twoTorsion : Finset G).erase 0))
        ((threeTorsion : Finset G).erase 0)
    _ = ((Finset.univ : Finset G).card * ((twoTorsion : Finset G).erase 0).card) *
        ((threeTorsion : Finset G).erase 0).card :=
      congrArg (fun k => k * ((threeTorsion : Finset G).erase 0).card)
        (Finset.card_product (Finset.univ : Finset G) ((twoTorsion : Finset G).erase 0))
    _ = _ := by rw [Finset.card_univ, Finset.card_erase_of_mem h0H, Finset.card_erase_of_mem h0K]









































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
      (@Couret.STROBO2TORS.exceptionalParams.{p2m_u_0} G inst inst_1 inst_2))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalParams_card

