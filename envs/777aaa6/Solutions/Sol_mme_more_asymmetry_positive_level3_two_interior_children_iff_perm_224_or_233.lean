-- Prove2me | solution 1 for mme_more_asymmetry_positive_level3_two_interior_children_iff_perm_224_or_233
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T10:19:27.905567+00:00
-- url     : https://prove2.me/submissions/0792bf94-f678-4640-99e7-1142d87a5b67

import Definitions.Def_mme_more_asymmetry_shape_predicates

set_option autoImplicit false

theorem solution
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      IsPerm112 a₁ b₁ c₁ ∧ IsPerm112 a₂ b₂ c₂ ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      IsPerm224 i j k ∨ IsPerm233 i j k := by
  constructor
  · rintro ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, hi, hj, hk⟩
    rcases h₁ with h₁ | h₁ | h₁ <;>
      rcases h₂ with h₂ | h₂ | h₂ <;>
      rcases h₁ with ⟨ha₁, hb₁, hc₁⟩ <;>
      rcases h₂ with ⟨ha₂, hb₂, hc₂⟩ <;>
      simp only [ha₁, hb₁, hc₁, ha₂, hb₂, hc₂,
        IsPerm224, IsPerm233] at hi hj hk ⊢ <;>
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
