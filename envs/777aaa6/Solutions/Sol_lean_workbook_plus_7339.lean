-- Prove2me | solution 1 for lean_workbook_plus_7339
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:20.654139+00:00
-- url     : https://prove2.me/submissions/030b0611-66ec-474a-a5b6-6f78258160a0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ∃ u v : ℝ, u = (Real.sqrt 3 + 1) ^ (2 * n) ∧ v = (Real.sqrt 3 - 1) ^ (2 * n) := by
  norm_num
