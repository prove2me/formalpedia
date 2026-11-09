-- Prove2me | solution 1 for Couret.STROBO2TORS.squareFibre_card_two_h_iff_exception
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:01.686193+00:00
-- url     : https://prove2.me/submissions/0ea4c532-aa8c-4868-8746-b8c81fbdae90

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paired_orbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_reflected_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]































theorem paired_squareFibre_card (a b d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) :
    (squareFibre ({a, b, b + d} : Finset G)).card =
      if ((b - a) + (b - a)) + (b - a) = 0 ∨
        ((b - a) + (b - a)) + (b - a) = d then
        2 * (twoTorsion : Finset G).card else (twoTorsion : Finset G).card := by
  rw [paired_squareFibre_eq a b d hd hd0 hab]
  split_ifs with h3
  · rw [Finset.card_union_of_disjoint (paired_orbits_disjoint a b d hd hab),
      torsionOrbit_card _ (paired_support_card_three a b d hd hd0 hab),
      torsionOrbit_card _ (reflected_support_card_three a b d hd hd0 hab h3)]
    omega
  · exact torsionOrbit_card _ (paired_support_card_three a b d hd hd0 hab)







/-- A fibre has size 2h exactly when it contains an exceptional partner. -/
theorem p2m_local_squareFibre_card_two_h_iff_exception (S : Finset G) (hS : S.card = 3) :
    (squareFibre S).card = 2 * (twoTorsion : Finset G).card ↔
      ∃ T : Finset G, ExceptionalPartner S T := by
  constructor
  · intro hc
    by_contra hn
    have hne : ∀ T : Finset G, ¬ ExceptionalPartner S T := by
      intro T h; exact hn ⟨T, h⟩
    have heq := squareFibre_eq_orbit_of_no_exception S hS hne
    have hcard := torsionOrbit_card S hS
    have hpos := twoTorsion_card_pos (G := G)
    rw [heq, hcard] at hc
    omega
  · rintro ⟨T, he⟩
    obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := he
    rw [hs, paired_squareFibre_card a b d hd hd0 hab, if_pos h3]










/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    Iff
      (@Eq.{1} Nat
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
      (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun T =>
        @Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T) := @_root_.Couret.STROBO2TORS.p2m_local_squareFibre_card_two_h_iff_exception

