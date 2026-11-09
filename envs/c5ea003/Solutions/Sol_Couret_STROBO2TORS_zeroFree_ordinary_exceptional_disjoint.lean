-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFree_ordinary_exceptional_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:21:04.441401+00:00
-- url     : https://prove2.me/submissions/1bf4684b-95d0-479b-92c5-c5b107e871af

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_ordinary_exceptionalFibres_disjoint
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]





















theorem p2m_local_zeroFree_ordinary_exceptional_disjoint :
    Disjoint (zeroFreeOrdinaryFibres : Finset (Finset (Finset G)))
      zeroFreeExceptionalFibres := by
  apply Finset.disjoint_left.mpr
  intro R hO hE
  obtain ⟨F, hF, hFR⟩ := Finset.mem_image.mp hO
  obtain ⟨K, hK, hKR⟩ := Finset.mem_image.mp hE
  obtain ⟨hOrd, hFne⟩ := Finset.mem_filter.mp hF
  have hFullF : F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
    rw [nonemptyFullFibres_eq_union]
    exact Finset.mem_union.mpr (Or.inl hF)
  have hFullK : K ∈ (nonemptyFullFibres : Finset (Finset (Finset G))) := by
    rw [nonemptyFullFibres_eq_union]
    exact Finset.mem_union.mpr (Or.inr hK)
  have hFK : F = K := withoutZero_injective_on_nonemptyFullFibres hFullF hFullK
    (hFR.trans hKR.symm)
  rw [hFK] at hOrd
  exact (Finset.disjoint_left.mp (ordinary_exceptionalFibres_disjoint (G := G))) hOrd hK















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
  @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.partialOrder.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.instOrderBot.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFree_ordinary_exceptional_disjoint

