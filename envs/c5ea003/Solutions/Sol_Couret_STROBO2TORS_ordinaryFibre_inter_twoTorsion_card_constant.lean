-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibre_inter_twoTorsion_card_constant
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:23.563564+00:00
-- url     : https://prove2.me/submissions/954c194c-d662-4ac8-b615-4fd2435b8a55

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_inter_twoTorsion_translate
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_eq_orbit
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]





/-- The number j of support points in G[2] is constant on every
two-torsion translation orbit. -/
theorem inter_twoTorsion_card_translate (S : Finset G) (u : G)
    (hu : u + u = 0) :
    (translateSupport S u ∩ twoTorsion).card =
      (S ∩ (twoTorsion : Finset G)).card := by
  rw [inter_twoTorsion_translate S u hu]
  exact translateSupport_card _ _



/-- The integer j = |S ∩ G[2]| is intrinsic to an ordinary fibre,
rather than to the choice of a triple representing it. -/
theorem p2m_local_ordinaryFibre_inter_twoTorsion_card_constant
    (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G))))
    (S T : Finset G) (hS : S ∈ F) (hT : T ∈ F) :
    (S ∩ (twoTorsion : Finset G)).card =
      (T ∩ (twoTorsion : Finset G)).card := by
  obtain ⟨R, _, hOrbit⟩ := ordinaryFibre_eq_orbit F hF
  rw [hOrbit] at hS hT
  obtain ⟨u, hu, hSu⟩ := (mem_torsionOrbit R S).mp hS
  obtain ⟨v, hv, hTv⟩ := (mem_torsionOrbit R T).mp hT
  rw [hSu, hTv, inter_twoTorsion_card_translate R u hu,
    inter_twoTorsion_card_translate R v hv]





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
    ∀ (S T : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          F S →
        @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
            F T →
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
                (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
            (@Finset.card.{p2m_u_0} G
              (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) T
                (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibre_inter_twoTorsion_card_constant

