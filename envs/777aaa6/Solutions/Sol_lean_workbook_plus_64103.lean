-- Prove2me | solution 1 for lean_workbook_plus_64103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:15.336469+00:00
-- url     : https://prove2.me/submissions/71e36c2e-e669-47ad-be58-d50c7f06b875

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 1 < 5) : 1 * 23 * 4 - 5 = 87 := by
  norm_num
