-- Prove2me | solution 1 for PRSLatin.cayley_pairCount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:57:58.805245+00:00
-- url     : https://prove2.me/submissions/f7ef2ede-606e-4704-b591-7f455d926754

import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin
open Classical PRSLatin in
theorem solution (G : Type*) [Group G] [Fintype G] (j₁ j₂ p q : G) :
    pairCount (cayley G) j₁ j₂ p q = if p * j₁⁻¹ * j₂ = q then 1 else 0 := by
  classical
  unfold pairCount cayley
  -- the only row reading `p` in column `j₁` is `i = p j₁⁻¹`
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨p * j₁⁻¹, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩
      rw [← h1, mul_inv_cancel_right]
    · rintro rfl
      exact ⟨inv_mul_cancel_right p j₁, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨h1, h2⟩
    apply h
    rw [← h1, mul_inv_cancel_right, h2]
