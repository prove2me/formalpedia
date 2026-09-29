-- Prove2me | solution 1 for StoneDualityML.hammingDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T07:31:19.930094+00:00
-- url     : https://prove2.me/submissions/386c794c-8dc3-4d45-a062-49091c42ffa0

import Mathlib
import Definitions.Def_Bridges_StoneDualityMLCore

theorem solution (n : ℕ) (h₁ h₂ h₃ : Fin n → Bool) :
    StoneDualityML.hammingDist n h₁ h₃ ≤
      StoneDualityML.hammingDist n h₁ h₂ + StoneDualityML.hammingDist n h₂ h₃ := by
  unfold StoneDualityML.hammingDist
  have hsub :
      (Finset.univ.filter (fun x : Fin n => h₁ x ≠ h₃ x)) ⊆
        (Finset.univ.filter (fun x : Fin n => h₁ x ≠ h₂ x)) ∪
        (Finset.univ.filter (fun x : Fin n => h₂ x ≠ h₃ x)) := by
    intro x hx
    have hne := (Finset.mem_filter.mp hx).2
    by_cases heq : h₁ x = h₂ x
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun heq' => hne (heq.trans heq')⟩
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, heq⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
