-- Prove2me | solution 1 for lean_workbook_plus_29274
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:56:09.990275+00:00
-- url     : https://prove2.me/submissions/b689cc05-9500-41d0-be05-f2fc0dc58f43

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (μ : ℝ) : (4 / 3) * (4 * μ - 3) ^ 2 ≥ 0 := by
  (intros; positivity)
