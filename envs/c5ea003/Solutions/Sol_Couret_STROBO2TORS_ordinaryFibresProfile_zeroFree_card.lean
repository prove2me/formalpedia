-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibresProfile_zeroFree_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:00.929772+00:00
-- url     : https://prove2.me/submissions/b9367e18-266a-423b-85e6-da8808a2b234

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_inter_twoTorsion_card_constant
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]













/-- The zero-free size of an ordinary fibre in stratum j is h-j. -/
theorem p2m_local_ordinaryFibresProfile_zeroFree_card (j : ℕ) (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibresProfile j : Finset (Finset (Finset G)))) :
    (withoutZero F).card = (twoTorsion : Finset G).card - j := by
  obtain ⟨hOrd, S, hSF, hj⟩ := Finset.mem_filter.mp hF
  obtain ⟨R, hR3, hRF, hSize⟩ := ordinaryFibres_zeroFree_size F hOrd
  have hRmem : R ∈ F := by
    rw [← hRF]
    exact (mem_squareFibre R R).mpr ⟨hR3, fun _ => rfl⟩
  have hconst := ordinaryFibre_inter_twoTorsion_card_constant
    F hOrd R S hRmem hSF
  rw [hconst, hj] at hSize
  exact hSize

end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j : Nat) (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j) F →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) j) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibresProfile_zeroFree_card

