-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibre_eq_orbit
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:36.082825+00:00
-- url     : https://prove2.me/submissions/97389ed8-d34c-4b52-bc56-684df3a6ef63

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]







/-- Every ordinary labelled-square fibre is an entire 2-torsion orbit. -/
theorem p2m_local_ordinaryFibre_eq_orbit (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ S : Finset G, S.card = 3 ∧ F = torsionOrbit S := by
  obtain ⟨S, hS3, hSF, _⟩ := ordinaryFibres_zeroFree_size F hF
  have hcard := (Finset.mem_filter.mp hF).2
  have hno : ∀ T : Finset G, ¬ ExceptionalPartner S T := by
    intro T hex
    have hc := (squareFibre_card_two_h_iff_exception S hS3).mpr ⟨T, hex⟩
    rw [hSF] at hc
    have hh := twoTorsion_card_pos (G := G)
    omega
  refine ⟨S, hS3, ?_⟩
  rw [← hSF]
  exact squareFibre_eq_orbit_of_no_exception S hS3 hno







end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
      And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) F
          (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibre_eq_orbit

