-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupportsProfile_eq_params_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:10:27.440044+00:00
-- url     : https://prove2.me/submissions/b2c68c38-3683-4071-b737-bc53fba1b9a1

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/



/-- The exceptional-support stratum is precisely the image of its unique
parameter stratum. This does not yet evaluate its numerical cardinality. -/
theorem p2m_local_exceptionalSupportsProfile_eq_params_image (j : ℕ) :
    (exceptionalSupportsProfile (G := G) j) =
      (exceptionalParamsProfile (G := G) j).image paramSupport := by
  ext S
  constructor
  · intro hS
    obtain ⟨hProfile, hCard⟩ := Finset.mem_filter.mp hS
    obtain ⟨hS3, hj⟩ := (mem_tripleSupportsProfile S j).mp hProfile
    have hExceptional : S ∈ (exceptionalSupports : Finset (Finset G)) :=
      (mem_exceptionalSupports_card S).mpr ⟨hS3, hCard⟩
    rw [exceptionalSupports_eq_params_image] at hExceptional
    obtain ⟨p, hp, hpS⟩ := Finset.mem_image.mp hExceptional
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, hpS⟩
    simpa [hpS] using hj
  · intro hS
    obtain ⟨p, hp, hpS⟩ := Finset.mem_image.mp hS
    obtain ⟨hParam, hj⟩ := Finset.mem_filter.mp hp
    have hExceptional : S ∈ (exceptionalSupports : Finset (Finset G)) := by
      rw [exceptionalSupports_eq_params_image]
      exact Finset.mem_image.mpr ⟨p, hParam, hpS⟩
    obtain ⟨hS3, hCard⟩ := (mem_exceptionalSupports_card S).mp hExceptional
    apply Finset.mem_filter.mpr
    refine ⟨(mem_tripleSupportsProfile S j).mpr ⟨hS3, ?_⟩, hCard⟩
    simpa [hpS] using hj



/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (j : Nat),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j)
    (@Finset.image.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G) (Finset.{p2m_u_0} G)
      (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1)
      (@Couret.STROBO2TORS.exceptionalParamsProfile.{p2m_u_0} G inst inst_1 inst_2 j)) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupportsProfile_eq_params_image

