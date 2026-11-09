-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinarySupportsProfile_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:46.577754+00:00
-- url     : https://prove2.me/submissions/439fd64a-efd2-41ef-8411-3c9ecbe19de0

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
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]





/-- Mapping each ordinary support to its labelled-square fibre gives exactly
the ordinary fibres carrying that profile. -/
theorem p2m_local_ordinarySupportsProfile_image (j : ℕ) :
    (ordinarySupportsProfile (G := G) j).image squareFibre =
      ordinaryFibresProfile j := by
  ext F
  constructor
  · intro hF
    obtain ⟨S, hS, hSF⟩ := Finset.mem_image.mp hF
    obtain ⟨hProfile, hCard⟩ := Finset.mem_filter.mp hS
    obtain ⟨hS3, hj⟩ := (mem_tripleSupportsProfile S j).mp hProfile
    have hAll : squareFibre S ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
      Finset.mem_image.mpr ⟨S, (mem_tripleSupports S).mpr hS3, rfl⟩
    have hOrd : F ∈ (ordinaryFibres : Finset (Finset (Finset G))) := by
      rw [← hSF]
      exact Finset.mem_filter.mpr ⟨hAll, hCard⟩
    have hSelf : S ∈ F := by
      rw [← hSF]
      exact (mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩
    exact Finset.mem_filter.mpr ⟨hOrd, S, hSelf, hj⟩
  · intro hF
    obtain ⟨hOrd, S, hSF, hj⟩ := Finset.mem_filter.mp hF
    have hAll : F ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
      (Finset.mem_filter.mp hOrd).1
    have hEq : squareFibre S = F :=
      allSquareFibres_squareFibre_member F hAll S hSF
    obtain ⟨T, hT, hTF⟩ := Finset.mem_image.mp hAll
    have hS3 : S.card = 3 := by
      have hIn : S ∈ squareFibre T := by
        rw [hTF]
        exact hSF
      exact ((mem_squareFibre T S).mp hIn).1
    have hProfile : S ∈ tripleSupportsProfile j :=
      (mem_tripleSupportsProfile S j).mpr ⟨hS3, hj⟩
    have hCard : (squareFibre S).card = (twoTorsion : Finset G).card := by
      rw [hEq]
      exact (Finset.mem_filter.mp hOrd).2
    exact Finset.mem_image.mpr
      ⟨S, Finset.mem_filter.mpr ⟨hProfile, hCard⟩, hEq⟩



















/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j : Nat),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.image.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (fun a b =>
        @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2)
      (@Couret.STROBO2TORS.ordinarySupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j))
    (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2 j) := @_root_.Couret.STROBO2TORS.p2m_local_ordinarySupportsProfile_image

