-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalFibres_withoutZero_card_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:26.856202+00:00
-- url     : https://prove2.me/submissions/068af1d5-6ee8-4259-91be-023474eb598b

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_ge_two
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]





















































theorem exceptionalFibres_h_ge_two (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    2 ≤ (twoTorsion : Finset G).card := by
  obtain ⟨S, hS, _⟩ := Finset.mem_image.mp hF
  rw [exceptionalSupports_eq_params_image] at hS
  obtain ⟨⟨⟨a, d⟩, v⟩, hp, _⟩ := Finset.mem_image.mp hS
  obtain ⟨hd, hd0, _, _⟩ := (mem_exceptionalParams a d v).mp hp
  exact twoTorsion_card_ge_two d hd hd0

theorem p2m_local_exceptionalFibres_withoutZero_card_ge_two (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    2 ≤ (withoutZero F).card := by
  have hh := exceptionalFibres_h_ge_two F hF
  rcases exceptionalFibres_zeroFree_card F hF with h | h <;> omega























end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F)) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalFibres_withoutZero_card_ge_two

