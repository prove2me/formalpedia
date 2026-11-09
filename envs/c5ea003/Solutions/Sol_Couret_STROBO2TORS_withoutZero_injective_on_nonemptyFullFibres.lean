-- Prove2me | solution 1 for Couret.STROBO2TORS.withoutZero_injective_on_nonemptyFullFibres
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:03.050411+00:00
-- url     : https://prove2.me/submissions/ab96b0b5-183a-4a85-829f-704f4bd34c15

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]











/-- Outside the empty restriction, removing zero never identifies distinct fibres.
This includes both ordinary and exceptional cases, for arbitrary finite abelian groups. -/
theorem p2m_local_withoutZero_injective_on_nonemptyFullFibres :
    Set.InjOn (withoutZero : Finset (Finset G) → Finset (Finset G))
      (nonemptyFullFibres : Finset (Finset (Finset G))) := by
  intro F hF K hK heq
  obtain ⟨hFAll, hFne⟩ := Finset.mem_filter.mp hF
  obtain ⟨hKAll, _⟩ := Finset.mem_filter.mp hK
  obtain ⟨S, hS⟩ := hFne
  have hSK : S ∈ withoutZero K := by rw [← heq]; exact hS
  have hSF' : S ∈ F := (Finset.mem_filter.mp hS).1
  have hSK' : S ∈ K := (Finset.mem_filter.mp hSK).1
  exact (allSquareFibres_squareFibre_member F hFAll S hSF').symm.trans
    (allSquareFibres_squareFibre_member K hKAll S hSK')

























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
  @Set.InjOn.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1)
    (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.nonemptyFullFibres.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_withoutZero_injective_on_nonemptyFullFibres

