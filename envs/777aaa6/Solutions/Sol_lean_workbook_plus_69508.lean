-- Prove2me | solution 1 for lean_workbook_plus_69508
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:19.274641+00:00
-- url     : https://prove2.me/submissions/951e85c0-c6e2-446d-832d-560324260c7a

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (x : ℕ → ℝ) (h₀ : 0 < n)
    (h₁ : ∀ k, 1 ≤ k ∧ k ≤ n → x k - x 1 ≥ 0)
    (h₂ : ∀ k, 1 ≤ k ∧ k ≤ n → x k - x n ≤ 0) :
    ∀ k, 1 ≤ k ∧ k ≤ n → (x k - x 1) * (x k - x n) ≤ 0 := by
  intro k hk
  exact mul_nonpos_of_nonneg_of_nonpos (h₁ k hk) (h₂ k hk)
