-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinarySupportsProfile_preimage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:09:17.181593+00:00
-- url     : https://prove2.me/submissions/39184550-4ab4-4c28-bf2a-545db9d64ebd

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_inter_twoTorsion_card_constant
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]







/-- The inverse-image of an ordinary profile fibre contains exactly all its
h support triples; it cannot lose or gain supports of a different profile. -/
theorem p2m_local_ordinarySupportsProfile_preimage (j : ℕ) (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibresProfile j : Finset (Finset (Finset G)))) :
    (ordinarySupportsProfile (G := G) j).filter
      (fun S => squareFibre S = F) = F := by
  obtain ⟨hOrd, T, hT, hj⟩ := Finset.mem_filter.mp hF
  have hAll : F ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
    (Finset.mem_filter.mp hOrd).1
  have hCard : F.card = (twoTorsion : Finset G).card :=
    (Finset.mem_filter.mp hOrd).2
  ext S
  constructor
  · intro hS
    obtain ⟨hProfileSupp, hEq⟩ := Finset.mem_filter.mp hS
    obtain ⟨hProfile, _⟩ := Finset.mem_filter.mp hProfileSupp
    have hS3 := ((mem_tripleSupportsProfile S j).mp hProfile).1
    rw [← hEq]
    exact (mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩
  · intro hS
    obtain ⟨R, hR, hRF⟩ := Finset.mem_image.mp hAll
    have hS3 : S.card = 3 := by
      have hIn : S ∈ squareFibre R := by
        rw [hRF]
        exact hS
      exact ((mem_squareFibre R S).mp hIn).1
    have hSame := ordinaryFibre_inter_twoTorsion_card_constant
      F hOrd S T hS hT
    have hJ : (S ∩ (twoTorsion : Finset G)).card = j :=
      hSame.trans hj
    have hSF : squareFibre S = F :=
      allSquareFibres_squareFibre_member F hAll S hS
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_tripleSupportsProfile S j).mpr ⟨hS3, hJ⟩, ?_⟩
      rw [hSF]
      exact hCard
    · exact hSF

















/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





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
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} G)
        (fun S =>
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) F)
        (fun a =>
          @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 a) F)
        (@Couret.STROBO2TORS.ordinarySupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j))
      F := @_root_.Couret.STROBO2TORS.p2m_local_ordinarySupportsProfile_preimage

