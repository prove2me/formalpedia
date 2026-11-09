-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_le_reduced_of_q_le_three
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:41.648768+00:00
-- url     : https://prove2.me/submissions/8c7dfc1e-cea1-4892-b199-c2791371b91f

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_all_reduced_of_q_le_three
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





/-- When the doubling quotient has at most three classes, and h>=2,
every observed zero-free fibre has cardinality at most 2h-2. -/
theorem p2m_local_zeroFreeFullFibres_card_le_reduced_of_q_le_three
    (hq : (doublingImages : Finset G).card ≤ 3)
    (hh : 2 ≤ (twoTorsion : Finset G).card)
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.card ≤ 2 * (twoTorsion : Finset G).card - 2 := by
  rw [zeroFreeFullFibres_eq_union] at hF
  rcases Finset.mem_union.mp hF with hOrd | hExc
  · have hBound := zeroFreeOrdinaryFibres_card_le_twoTorsion F hOrd
    omega
  · have hCard := zeroFreeExceptionalFibres_all_reduced_of_q_le_three hq F hExc
    omega






















end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
      ∀ (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
        @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
              (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
            (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) F →
          @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_le_reduced_of_q_le_three

