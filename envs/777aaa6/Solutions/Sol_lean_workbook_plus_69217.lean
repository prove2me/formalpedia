-- Prove2me | solution 1 for lean_workbook_plus_69217
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:00.201407+00:00
-- url     : https://prove2.me/submissions/060d2a22-3618-41fc-9bd3-98d9ff853156

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx: x 1 = 1 ∧ x 2 = 1 ∧ ∀ n, x (n + 2) = x (n + 1) + (n + 1) * x n) : ∃ l, ∑' n : ℕ, ((n:ℝ)^2 / (x n + 1)) = l := by
  norm_num
