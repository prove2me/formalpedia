-- Prove2me | solution 1 for lean_workbook_plus_82033
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:05.194173+00:00
-- url     : https://prove2.me/submissions/78c5174b-f75c-4697-80c8-88a712427034

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (M : ℝ) (x : ℕ → ℝ) (hM : 0 ≤ M) (hx : ∀ n, |x n| ≤ M)
    (h'x : ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |x (n + 1) - x n| < ε) :
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |x (n + 1) - x n| < ε := by
  (intros; simp_all)
