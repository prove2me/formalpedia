-- Prove2me | solution 1 for Couret.STROBO2TORS.allSquareFibres_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:48.961179+00:00
-- url     : https://prove2.me/submissions/2f00b454-1270-4eef-957d-d3d4647d37df

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_eq_all_filter
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]













































































theorem p2m_local_allSquareFibres_eq_union :
    (allSquareFibres : Finset (Finset (Finset G))) = ordinaryFibres ∪ exceptionalFibres := by
  ext F
  constructor
  · intro hF
    obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
    have hs3 := (mem_tripleSupports S).mp hS
    rcases squareFibre_card_h_or_two_h S hs3 with hc | hc
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S, hS, hsF⟩,
        by rw [← hsF]; exact hc⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨S, (mem_exceptionalSupports_card S).mpr ⟨hs3, hc⟩, hsF⟩
  · intro hF
    rcases Finset.mem_union.mp hF with hF | hF
    · exact (Finset.mem_filter.mp hF).1
    · rw [exceptionalFibres_eq_all_filter] at hF
      exact (Finset.mem_filter.mp hF).1











end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.allSquareFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun a b =>
        @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)
      (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_allSquareFibres_eq_union

