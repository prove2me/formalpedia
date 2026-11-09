-- Prove2me | solution 1 for Couret.STROBO2TORS.nonemptyFullFibres_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:15:36.02199+00:00
-- url     : https://prove2.me/submissions/5c3a04fb-5e52-40d6-9cd8-5db9e109d889

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_withoutZero_card_ge_two
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

















/-- The full fibre set is a disjoint partition into surviving ordinary
fibres and exceptional fibres, before applying removal of zero. -/
theorem p2m_local_nonemptyFullFibres_eq_union :
    (nonemptyFullFibres : Finset (Finset (Finset G))) =
      ordinaryNonemptyFibres ∪ exceptionalFibres := by
  ext F
  constructor
  · intro hh
    obtain ⟨hAll, hne⟩ := Finset.mem_filter.mp hh
    rw [allSquareFibres_eq_union] at hAll
    rcases Finset.mem_union.mp hAll with hO | hE
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hO, hne⟩))
    · exact Finset.mem_union.mpr (Or.inr hE)
  · intro hh
    rcases Finset.mem_union.mp hh with hO | hE
    · obtain ⟨hO, hne⟩ := Finset.mem_filter.mp hO
      have hAll : F ∈ (allSquareFibres : Finset (Finset (Finset G))) := by
        rw [allSquareFibres_eq_union]
        exact Finset.mem_union.mpr (Or.inl hO)
      exact Finset.mem_filter.mpr ⟨hAll, hne⟩
    · have hAll : F ∈ (allSquareFibres : Finset (Finset (Finset G))) := by
        rw [allSquareFibres_eq_union]
        exact Finset.mem_union.mpr (Or.inr hE)
      have hge := exceptionalFibres_withoutZero_card_ge_two F hE
      have hne : (withoutZero F).Nonempty :=
        Finset.card_pos.mp (by omega)
      exact Finset.mem_filter.mpr ⟨hAll, hne⟩



















/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.nonemptyFullFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Finset.instUnion.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun a b =>
        @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.ordinaryNonemptyFibres.{p2m_u_0} G inst inst_1 inst_2)
      (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_nonemptyFullFibres_eq_union

