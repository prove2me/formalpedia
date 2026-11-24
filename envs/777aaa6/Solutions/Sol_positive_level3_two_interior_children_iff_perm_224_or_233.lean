-- Prove2me | solution 1 for positive_level3_two_interior_children_iff_perm_224_or_233
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T05:02:47.648772+00:00
-- url     : https://prove2.me/submissions/d0f7d92b-4eec-40f8-a439-cb5ab68ae975

import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      ((a₁ = 1 ∧ b₁ = 1 ∧ c₁ = 2) ∨ (a₁ = 1 ∧ b₁ = 2 ∧ c₁ = 1) ∨ (a₁ = 2 ∧ b₁ = 1 ∧ c₁ = 1)) ∧
      ((a₂ = 1 ∧ b₂ = 1 ∧ c₂ = 2) ∨ (a₂ = 1 ∧ b₂ = 2 ∧ c₂ = 1) ∨ (a₂ = 2 ∧ b₂ = 1 ∧ c₂ = 1)) ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      ((i = 2 ∧ j = 2 ∧ k = 4) ∨ (i = 2 ∧ j = 4 ∧ k = 2) ∨ (i = 4 ∧ j = 2 ∧ k = 2)) ∨
      ((i = 2 ∧ j = 3 ∧ k = 3) ∨ (i = 3 ∧ j = 2 ∧ k = 3) ∨ (i = 3 ∧ j = 3 ∧ k = 2)) := by
  constructor
  · rintro ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, hi, hj, hk⟩
    rcases h₁ with h₁ | h₁ | h₁ <;>
      rcases h₂ with h₂ | h₂ | h₂ <;>
      rcases h₁ with ⟨ha₁, hb₁, hc₁⟩ <;>
      rcases h₂ with ⟨ha₂, hb₂, hc₂⟩ <;>
      simp only [ha₁, hb₁, hc₁, ha₂, hb₂, hc₂] at hi hj hk ⊢ <;>
      omega
  · intro h
    rcases h with h | h
    · rcases h with h | h | h
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨1, 1, 2, 1, 1, 2, Or.inl ⟨rfl, rfl, rfl⟩,
          Or.inl ⟨rfl, rfl, rfl⟩, by omega, by omega, by omega⟩
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨1, 2, 1, 1, 2, 1, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by omega, by omega, by omega⟩
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨2, 1, 1, 2, 1, 1, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), by omega, by omega, by omega⟩
    · rcases h with h | h | h
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨1, 1, 2, 1, 2, 1, Or.inl ⟨rfl, rfl, rfl⟩,
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by omega, by omega, by omega⟩
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨1, 1, 2, 2, 1, 1, Or.inl ⟨rfl, rfl, rfl⟩,
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), by omega, by omega, by omega⟩
      · rcases h with ⟨hi, hj, hk⟩
        exact ⟨2, 1, 1, 1, 2, 1, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by omega, by omega, by omega⟩

#check @solution
