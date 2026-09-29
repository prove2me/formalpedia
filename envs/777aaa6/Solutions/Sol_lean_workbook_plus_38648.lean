-- Prove2me | solution 1 for lean_workbook_plus_38648
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:51:50.502695+00:00
-- url     : https://prove2.me/submissions/f0db5366-5323-4f29-ac0a-8ac2498abb2c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : (a + b) ^ 4 ≥ 1 ^ 4) : a ^ 4 + b ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 ≥ 1 := by
  (intros; linarith)
