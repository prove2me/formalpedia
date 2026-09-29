-- Prove2me | solution 1 for lean_workbook_plus_1536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:00.939671+00:00
-- url     : https://prove2.me/submissions/69fe1cb1-cbf7-4d7d-b949-1cba1ae4df24

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) : (∃ x_1 x_2 x_3 x_4 :ℝ, x_1 + x_2 * x_3 * x_4 = 2 ∧ x_2 + x_3 * x_4 * x_1 = 2 ∧ x_3 + x_4 * x_1 * x_2 = 2 ∧ x_4 + x_1 * x_2 * x_3 = 2) ↔ (∃ x_1 x_2 x_3 x_4 :ℝ, x_1 + x_2 * x_3 * x_4 = 2 ∧ x_2 + x_3 * x_4 * x_1 = 2 ∧ x_3 + x_4 * x_1 * x_2 = 2 ∧ x_4 + x_1 * x_2 * x_3 = 2) := by
  norm_num
