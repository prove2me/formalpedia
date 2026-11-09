-- Prove2me | solution 1 for Couret.InterIA.Cubic.small_family_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:00.840203+00:00
-- url     : https://prove2.me/submissions/29672eae-9b52-498b-8b4d-c4cea426f30c

import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Cubic



theorem p2m_local_small_family_probes {α ι : Type*} (q : α → ι → ℝ) (F : Set α)
    (hinj : Set.InjOn q F) (hcard : F.ncard=1 ∨ F.ncard=2) :
    ∃ Q : Finset ι, Q.card≤2 ∧ Separates q F Q := by
  classical
  rcases hcard with h|h
  · obtain ⟨A,rfl⟩ := Set.ncard_eq_one.mp h
    refine ⟨∅,by simp,?_⟩
    intro B hB C hC _
    simpa only [Set.mem_singleton_iff] using hB.trans hC.symm
  · obtain ⟨A,B,hAB,rfl⟩ := Set.ncard_eq_two.mp h
    have hne : q A ≠ q B := by
      intro he
      exact hAB (hinj (by simp) (by simp) he)
    obtain ⟨z,hz⟩ : ∃ z, q A z ≠ q B z := by
      by_contra! he
      exact hne (funext he)
    refine ⟨{z},by simp,?_⟩
    intro C hC D hD he
    have hez := he z (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hC hD
    rcases hC with rfl|rfl <;> rcases hD with rfl|rfl
    · rfl
    · exact False.elim (hz hez)
    · exact False.elim (hz hez.symm)
    · rfl



end Couret.InterIA.Cubic

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {α : Type p2m_u_0} {ι : Type p2m_u_1} (q : α → ι → Real) (F : Set.{p2m_u_0} α),
  @Set.InjOn.{p2m_u_0, p2m_u_1} α (ι → Real) q F →
    Or (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} α F) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat (@Set.ncard.{p2m_u_0} α F) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      @Exists.{p2m_u_1 + 1} (Finset.{p2m_u_1} ι) fun Q =>
        And
          (@LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_1} ι Q)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Couret.InterIA.Cubic.Separates.{p2m_u_0, p2m_u_1} α ι q F Q) := @_root_.Couret.InterIA.Cubic.p2m_local_small_family_probes

