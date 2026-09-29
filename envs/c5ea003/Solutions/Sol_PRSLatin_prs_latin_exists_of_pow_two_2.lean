-- Prove2me | solution 2 for PRSLatin.prs_latin_exists_of_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:47:39.767902+00:00
-- url     : https://prove2.me/submissions/8aa8a7f2-51f5-4d9b-92ed-d4c5d6e284f4

import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin
open PRSLatin in
theorem solution (k : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (L : α → α → α),
      Nat.card α = 2 ^ k ∧ IsLatin L ∧ IsPRS L ∧ IsIndexLeOne L := by
  -- the addition table of `(ZMod 2)^k`
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have hself : ∀ x : Fin k → ZMod 2, x + x = 0 := fun x => funext fun i => h2 (x i)
  refine ⟨Fin k → ZMod 2, inferInstance, fun i j => i + j, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · exact ⟨fun i => (Equiv.addLeft i).bijective, fun j => (Equiv.addRight j).bijective⟩
  · -- `i ↦ i + (j₁ + j₂)` swaps the rows reading `(p, q)` and `(q, p)`
    intro j₁ j₂ p q
    unfold pairCount
    apply Finset.card_nbij' (· + (j₁ + j₂)) (· + (j₁ + j₂))
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      obtain ⟨h1, h2'⟩ := hi
      constructor
      · rw [← h2']
        calc i + (j₁ + j₂) + j₁ = i + j₂ + (j₁ + j₁) := by abel
          _ = i + j₂ := by rw [hself, add_zero]
      · rw [← h1]
        calc i + (j₁ + j₂) + j₂ = i + j₁ + (j₂ + j₂) := by abel
          _ = i + j₁ := by rw [hself, add_zero]
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      obtain ⟨h1, h2'⟩ := hi
      constructor
      · rw [← h2']
        calc i + (j₁ + j₂) + j₁ = i + j₂ + (j₁ + j₁) := by abel
          _ = i + j₂ := by rw [hself, add_zero]
      · rw [← h1]
        calc i + (j₁ + j₂) + j₂ = i + j₁ + (j₂ + j₂) := by abel
          _ = i + j₁ := by rw [hself, add_zero]
    · intro i _
      simp only
      rw [add_assoc, hself, add_zero]
    · intro i _
      simp only
      rw [add_assoc, hself, add_zero]
  · intro j₁ j₂ _ i i' h
    simp only [Prod.mk.injEq] at h
    exact add_right_cancel h.1
