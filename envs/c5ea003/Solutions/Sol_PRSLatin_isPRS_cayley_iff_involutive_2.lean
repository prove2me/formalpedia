-- Prove2me | solution 2 for PRSLatin.isPRS_cayley_iff_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:52:49.487596+00:00
-- url     : https://prove2.me/submissions/6414a4cc-59d8-4f66-9a74-79eb30961a08

import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin
open PRSLatin in
theorem solution (G : Type*) [Group G] [Fintype G] :
    IsPRS (cayley G) ↔ ∀ x : G, x * x = 1 := by
  classical
  -- the pair count of the Cayley table is `[p j₁⁻¹ j₂ = q]`
  have hpc : ∀ j₁ j₂ p q : G,
      pairCount (cayley G) j₁ j₂ p q = if p * j₁⁻¹ * j₂ = q then 1 else 0 := by
    intro j₁ j₂ p q
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
  unfold IsPRS
  simp only [hpc]
  constructor
  · -- columns `1, x` and symbols `(1, x)`: the reversed pair forces `x x = 1`
    intro h x
    have := h 1 x 1 x
    simp only [inv_one, mul_one, one_mul, if_true] at this
    by_contra hx
    rw [if_neg hx] at this
    exact one_ne_zero this
  · -- with `g = j₁⁻¹ j₂` an involution, `p g = q ↔ q g = p`
    intro h j₁ j₂ p q
    have hg : j₁⁻¹ * j₂ * (j₁⁻¹ * j₂) = 1 := h _
    have key : p * j₁⁻¹ * j₂ = q ↔ q * j₁⁻¹ * j₂ = p := by
      constructor
      · rintro rfl
        calc p * j₁⁻¹ * j₂ * j₁⁻¹ * j₂ = p * (j₁⁻¹ * j₂ * (j₁⁻¹ * j₂)) := by group
          _ = p := by rw [hg, mul_one]
      · rintro rfl
        calc q * j₁⁻¹ * j₂ * j₁⁻¹ * j₂ = q * (j₁⁻¹ * j₂ * (j₁⁻¹ * j₂)) := by group
          _ = q := by rw [hg, mul_one]
    by_cases hpq : p * j₁⁻¹ * j₂ = q
    · rw [if_pos hpq, if_pos (key.mp hpq)]
    · rw [if_neg hpq, if_neg (fun h' => hpq (key.mpr h'))]
