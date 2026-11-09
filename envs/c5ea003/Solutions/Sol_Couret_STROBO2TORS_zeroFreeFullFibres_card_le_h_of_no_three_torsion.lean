-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_le_h_of_no_three_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:43.616922+00:00
-- url     : https://prove2.me/submissions/7348167e-f834-41b7-99d8-7d67670c7b15

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]



/-- In the absence of nonzero 3-torsion, the exact general upper bound
improves from 2h to h, for every finite abelian group. -/
theorem p2m_local_zeroFreeFullFibres_card_le_h_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1)
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.card ≤ (twoTorsion : Finset G).card := by
  rw [zeroFreeFullFibres_eq_union,
    zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion ht] at hF
  have hOrd : F ∈ (zeroFreeOrdinaryFibres : Finset (Finset (Finset G))) := by
    simpa using hF
  exact zeroFreeOrdinaryFibres_card_le_twoTorsion F hOrd
























end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    ∀ (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
          (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) F →
        @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_le_h_of_no_three_torsion

