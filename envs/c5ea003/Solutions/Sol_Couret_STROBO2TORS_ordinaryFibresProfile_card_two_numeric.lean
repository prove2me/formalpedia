-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibresProfile_card_two_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:52.159767+00:00
-- url     : https://prove2.me/submissions/4d1d50a6-f885-4690-9a7e-50eb46c679dc

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_two_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_sub_div
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/



/-- Profile-two full ordinary fibres, including groups with small H.
This is not yet an aggregate zero-free histogram theorem. -/
theorem p2m_local_ordinaryFibresProfile_card_two_numeric :
    (ordinaryFibresProfile (G := G) 2).card =
      ((twoTorsion : Finset G).card.choose 2 *
        ((Fintype.card G - (twoTorsion : Finset G).card).choose 1) -
        ((twoTorsion : Finset G).card *
          ((twoTorsion : Finset G).card - 1) *
          ((threeTorsion : Finset G).card - 1))) /
        (twoTorsion : Finset G).card := by
  rw [ordinaryFibresProfile_card_sub_div 2 (by omega),
    exceptionalSupportsProfile_two_card]

end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (Nat.choose (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Nat.choose
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibresProfile_card_two_numeric

