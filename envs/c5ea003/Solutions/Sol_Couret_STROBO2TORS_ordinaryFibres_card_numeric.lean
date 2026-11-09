-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_card_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:10.956956+00:00
-- url     : https://prove2.me/submissions/da73456d-782b-48e1-b514-dd6cd8d21923

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_weighted_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]





















































































theorem ordinaryFibres_card :
    (ordinaryFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card -
        2 * (exceptionalFibres : Finset (Finset (Finset G))).card := by
  have hd : (Fintype.card G).choose 3 / (twoTorsion : Finset G).card =
      (ordinaryFibres (G := G)).card + 2 * (exceptionalFibres (G := G)).card := by
    rw [tripleSupports_weighted_card]
    exact Nat.mul_div_cancel_left _ (twoTorsion_card_pos (G := G))
  rw [hd]
  omega

theorem p2m_local_ordinaryFibres_card_numeric :
    (ordinaryFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card -
        2 * ((Fintype.card G / (twoTorsion : Finset G).card) *
          ((twoTorsion : Finset G).card - 1) * (((threeTorsion : Finset G).card - 1) / 2)) := by
  rw [ordinaryFibres_card, exceptionalFibres_card_numeric]

end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Nat.choose (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@Fintype.card.{p2m_u_0} G inst_2)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_card_numeric

