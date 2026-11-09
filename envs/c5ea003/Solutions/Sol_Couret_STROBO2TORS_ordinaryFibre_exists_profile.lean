-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibre_exists_profile
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:09.453934+00:00
-- url     : https://prove2.me/submissions/1d4205c9-9edd-4712-bc6b-5d7d15597d7b

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_eq_orbit
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- A genuine ordinary fibre belongs to the profile determined by any of its supports. -/
theorem ordinaryFibre_mem_profile_of_member
    (F : Finset (Finset G)) (S : Finset G) (j : ℕ)
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G))))
    (hS : S ∈ F)
    (hj : (S ∩ (twoTorsion : Finset G)).card = j) :
    F ∈ (ordinaryFibresProfile j : Finset (Finset (Finset G))) := by
  exact Finset.mem_filter.mpr ⟨hF, S, hS, hj⟩



/-- There is a profile bounded by the size of the three-element support. -/
theorem p2m_local_ordinaryFibre_exists_profile
    (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ j : ℕ, j ≤ 3 ∧
      F ∈ (ordinaryFibresProfile j : Finset (Finset (Finset G))) := by
  obtain ⟨S, hS3, hOrbit⟩ := ordinaryFibre_eq_orbit F hF
  have hS : S ∈ F := by
    rw [hOrbit]
    exact (mem_torsionOrbit S S).mpr ⟨0, by simp, by simp [translateSupport]⟩
  let j := (S ∩ (twoTorsion : Finset G)).card
  refine ⟨j, ?_, ?_⟩
  · exact le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq hS3)
  · exact ordinaryFibre_mem_profile_of_member F S j hF hS rfl



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    @Exists.{1} Nat fun j =>
      And (@LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
          (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j) F) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibre_exists_profile

