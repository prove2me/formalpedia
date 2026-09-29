-- Prove2me | solution 1 for lean_workbook_plus_16402
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:10.544582+00:00
-- url     : https://prove2.me/submissions/2ec51969-1f19-4d79-ac64-96b8edf378f9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a n : ℕ) : (a : ℝ) ≥ 1 / 2 ^ n → (a : ℝ) ^ (1 - 1 / n) ≤ 2 * a ∧ (a : ℝ) < 1 / 2 ^ n → (a : ℝ) ^ (1 - 1 / n) < 2 * a + 1 / 2 ^ (n - 1) := by
  (intros; linarith)
