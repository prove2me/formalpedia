-- Prove2me | solution 1 for lean_workbook_plus_28337
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:43:14.659112+00:00
-- url     : https://prove2.me/submissions/a8b7b9e4-8303-4e19-9b9d-c7f9b7e52219

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℕ → ℕ)
  (b : ℕ → ℕ)
  (h₀ : b 0 = 1)
  (h₁ : b 1 = 5)
  (h₂ : ∀ n ≥ 2, b n = 4 * b (n - 1) - b (n - 2))
  (h₃ : ∀ n, Odd (b n))
  (h₄ : ∀ n, a n = (b n + 1)^2 / 2^2 + (b n - 1)^2 / 2^2) :
  ∀ n, ∃ x y : ℕ, a n = x^2 + y^2 := by
  intro n
  obtain ⟨k, hk⟩ := h₃ n
  refine ⟨k + 1, k, ?_⟩
  rw [h₄ n, hk]
  have e1 : (2 * k + 1 + 1)^2 = (k + 1)^2 * 2^2 := by ring
  have e2 : (2 * k + 1 - 1)^2 = k^2 * 2^2 := by
    rw [Nat.add_sub_cancel]
    ring
  rw [e1, e2, Nat.mul_div_cancel _ (by norm_num), Nat.mul_div_cancel _ (by norm_num)]
