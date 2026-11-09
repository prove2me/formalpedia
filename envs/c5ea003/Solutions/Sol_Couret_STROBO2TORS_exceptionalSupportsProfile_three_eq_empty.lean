-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupportsProfile_three_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:10:44.811392+00:00
-- url     : https://prove2.me/submissions/4f10aa70-fb26-43fc-9ce7-ab65dd7b3cdd

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
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]





















/-- The exceptional support normal form has either zero, one or two
vertices in the two-torsion subgroup, never three. -/
theorem p2m_local_exceptionalSupportsProfile_three_eq_empty :
    (exceptionalSupportsProfile (G := G) 3) = ∅ := by
  ext S
  constructor
  · intro hS
    obtain ⟨hProfile, hCard⟩ := Finset.mem_filter.mp hS
    obtain ⟨hS3, hSJ⟩ := (mem_tripleSupportsProfile S 3).mp hProfile
    have hExceptional : S ∈ (exceptionalSupports : Finset (Finset G)) :=
      (mem_exceptionalSupports_card S).mpr ⟨hS3, hCard⟩
    rw [exceptionalSupports_eq_params_image] at hExceptional
    obtain ⟨⟨⟨a, d⟩, v⟩, hp, hs⟩ := Finset.mem_image.mp hExceptional
    obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hp
    have hsize := paramSupport_inter_twoTorsion_card a d v hd hd0 hv hv0
    rw [hs, hSJ] at hsize
    split_ifs at hsize <;> omega
  · intro h
    simp at h



/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instEmptyCollection.{p2m_u_0} (Finset.{p2m_u_0} G))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupportsProfile_three_eq_empty

