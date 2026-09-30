-- Prove2me | solution 1 for lean_workbook_plus_58717
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:23:38.493839+00:00
-- url     : https://prove2.me/submissions/57ce2e75-c14b-4dea-8cbc-12a86d7c30fb

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (α : ℤ) (hf: f = (λ x:ℤ => 20 * x ^ 2 - 11 * x + 2016)) : (¬ 2 ^ 10 ^ 11 ^ 2016 ∣ f α) ∨ ∃ α : ℤ, (2 ^ 10 ^ 11 ^ 2016 ∣ f α) := by
  by_cases h : (2 : ℤ) ^ 10 ^ 11 ^ 2016 ∣ f α
  · exact Or.inr ⟨α, h⟩
  · exact Or.inl h
