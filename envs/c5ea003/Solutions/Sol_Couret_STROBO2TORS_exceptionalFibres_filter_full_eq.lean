-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalFibres_filter_full_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:50.229699+00:00
-- url     : https://prove2.me/submissions/bc473c02-8539-409c-a3e6-3c74d0323fd5

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_zeroFree_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroContainingExceptionalSupports_preimage
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]



















theorem exceptionalFibres_zeroContaining_card (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    (F.filter (fun S => 0 ∈ S)).card = 0 ∨ (F.filter (fun S => 0 ∈ S)).card = 2 := by
  have hc := Finset.card_filter_add_card_filter_not (s := F) (fun S : Finset G => 0 ∈ S)
  have hf := exceptionalFibres_member_card F hF
  change (F.filter (fun S => 0 ∈ S)).card + (withoutZero F).card = F.card at hc
  rcases exceptionalFibres_zeroFree_card F hF with h | h <;> omega















theorem zeroHitExceptionalFibres_subset :
    (zeroHitExceptionalFibres : Finset (Finset (Finset G))) ⊆ exceptionalFibres := by
  intro F hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
  exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, hsF⟩



theorem zeroHitExceptionalFibres_member_zeroContaining_card (F : Finset (Finset G))
    (hF : F ∈ (zeroHitExceptionalFibres : Finset (Finset (Finset G)))) :
    (F.filter (fun S => 0 ∈ S)).card = 2 := by
  have hFE := zeroHitExceptionalFibres_subset hF
  obtain ⟨S, hS, hsF⟩ := Finset.mem_image.mp hF
  have hp : S ∈ zeroContainingExceptionalSupports.filter (fun T : Finset G => squareFibre T = F) :=
    Finset.mem_filter.mpr ⟨hS, hsF⟩
  rw [zeroContainingExceptionalSupports_preimage F hFE] at hp
  have hn := Finset.card_pos.mpr ⟨S, hp⟩
  rcases exceptionalFibres_zeroContaining_card F hFE with h | h <;> omega







theorem mem_zeroHitExceptionalFibres (F : Finset (Finset G)) :
    F ∈ (zeroHitExceptionalFibres : Finset (Finset (Finset G))) ↔
      F ∈ exceptionalFibres ∧ (F.filter (fun S => 0 ∈ S)).Nonempty := by
  constructor
  · intro hF
    have hFE := zeroHitExceptionalFibres_subset hF
    have hc := zeroHitExceptionalFibres_member_zeroContaining_card F hF
    exact ⟨hFE, Finset.card_pos.mp (by omega)⟩
  · rintro ⟨hFE, S, hS⟩
    rw [← zeroContainingExceptionalSupports_preimage F hFE] at hS
    obtain ⟨hS, hsF⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_image.mpr ⟨S, hS, hsF⟩

theorem zeroHitExceptionalFibres_member_card (F : Finset (Finset G))
    (hF : F ∈ (zeroHitExceptionalFibres : Finset (Finset (Finset G)))) :
    (withoutZero F).card = 2 * (twoTorsion : Finset G).card - 2 := by
  have hc := Finset.card_filter_add_card_filter_not (s := F) (fun S : Finset G => 0 ∈ S)
  change (F.filter (fun S => 0 ∈ S)).card + (withoutZero F).card = F.card at hc
  have h0 := zeroHitExceptionalFibres_member_zeroContaining_card F hF
  have hf := exceptionalFibres_member_card F (zeroHitExceptionalFibres_subset hF)
  omega

theorem zeroMissingExceptionalFibres_member_card (F : Finset (Finset G))
    (hF : F ∈ (zeroMissingExceptionalFibres : Finset (Finset (Finset G)))) :
    (withoutZero F).card = 2 * (twoTorsion : Finset G).card := by
  obtain ⟨hFE, hFn⟩ := Finset.mem_sdiff.mp hF
  have h0 : (F.filter (fun S => 0 ∈ S)).card = 0 := by
    rcases exceptionalFibres_zeroContaining_card F hFE with h | h
    · exact h
    · have hn : (F.filter (fun S => 0 ∈ S)).Nonempty := Finset.card_pos.mp (by omega)
      exact (hFn ((mem_zeroHitExceptionalFibres F).mpr ⟨hFE, hn⟩)).elim
  have hc := Finset.card_filter_add_card_filter_not (s := F) (fun S : Finset G => 0 ∈ S)
  change (F.filter (fun S => 0 ∈ S)).card + (withoutZero F).card = F.card at hc
  have hf := exceptionalFibres_member_card F hFE
  omega















theorem p2m_local_exceptionalFibres_filter_full_eq :
    (exceptionalFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = 2 * (twoTorsion : Finset G).card) =
      zeroMissingExceptionalFibres := by
  ext F
  constructor
  · intro h
    obtain ⟨hFE, hc⟩ := Finset.mem_filter.mp h
    apply Finset.mem_sdiff.mpr
    refine ⟨hFE, ?_⟩
    intro hh
    have hr := zeroHitExceptionalFibres_member_card F hh
    have hp := twoTorsion_card_pos (G := G)
    omega
  · intro h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1,
      zeroMissingExceptionalFibres_member_card F h⟩











end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (fun F =>
        @Eq.{1} Nat
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
      (fun a =>
        instDecidableEqNat
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
      (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2))
    (@Couret.STROBO2TORS.zeroMissingExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalFibres_filter_full_eq

