-- Prove2me | solution 1 for Couret.STROBO2TORS.tripleSupportsProfile_ordinary_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:00.649146+00:00
-- url     : https://prove2.me/submissions/bd52988d-9586-4bc0-b6e4-fa58bec5a9ac

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]











/-- The profile supports split into those with ordinary and exceptional
complete fibres, regardless of whether the zero-free restriction is empty. -/
theorem p2m_local_tripleSupportsProfile_ordinary_exceptional (j : ℕ) :
    (tripleSupportsProfile (G := G) j) =
      ordinarySupportsProfile j ∪ exceptionalSupportsProfile j := by
  ext S
  constructor
  · intro hS
    have hS3 := ((mem_tripleSupportsProfile S j).mp hS).1
    rcases squareFibre_card_h_or_two_h S hS3 with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hS, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hS, h⟩))
  · intro hS
    rcases Finset.mem_union.mp hS with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1













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
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.tripleSupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j)
    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} G) fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
      (@Couret.STROBO2TORS.ordinarySupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j)
      (@Couret.STROBO2TORS.exceptionalSupportsProfile.{p2m_u_0} G inst inst_1 inst_2 j)) := @_root_.Couret.STROBO2TORS.p2m_local_tripleSupportsProfile_ordinary_exceptional

