-- Prove2me | solution 1 for lean_workbook_plus_50385
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:44.263588+00:00
-- url     : https://prove2.me/submissions/3422f578-66fd-43fe-9991-a27469b65b2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (x2 : 0 < x 2) (h : ∀ n, x (n + 1) = -1 + (1 + n * x n) ^ (1 / n)) : ∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |n * x n| < ε := by
  (intros; simp_all)
