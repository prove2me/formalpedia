-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeExceptionalFibres_all_reduced_of_q_le_three
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:13.667798+00:00
-- url     : https://prove2.me/submissions/4652bde3-5370-4b90-8b01-1f6cfba9e2c0

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_nonempty_iff
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]













































































theorem p2m_local_zeroFreeExceptionalFibres_all_reduced_of_q_le_three
    (hq : (doublingImages : Finset G).card ≤ 3) (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeExceptionalFibres : Finset (Finset (Finset G)))) :
    F.card = 2 * (twoTorsion : Finset G).card - 2 := by
  obtain ⟨K, hK, hkF⟩ := Finset.mem_image.mp hF
  rcases exceptionalFibres_zeroFree_card K hK with hr | hf
  · rwa [hkF] at hr
  · have hn : ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
        (fun F => F.card = 2 * (twoTorsion : Finset G).card)).Nonempty := by
      refine ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨K, hK, hkF⟩, ?_⟩⟩
      rwa [hkF] at hf
    have hp := ((zeroFreeExceptionalFibres_full_nonempty_iff (G := G)).mp hn).1
    omega

end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    ∀ (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
          (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) F →
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeExceptionalFibres_all_reduced_of_q_le_three

