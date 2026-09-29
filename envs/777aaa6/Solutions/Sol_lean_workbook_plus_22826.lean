-- Prove2me | solution 1 for lean_workbook_plus_22826
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:18.004577+00:00
-- url     : https://prove2.me/submissions/1ece5bb5-2c06-4f0f-8fe0-7bfbcb8a76e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (x : ℝ) (g_def : g x = 3 * x + 1) (x_in : x ∈ Set.Icc (-3) 2) : ∃ y, y = g x := by
  norm_num
