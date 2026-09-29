-- Prove2me | solution 1 for lean_workbook_plus_42574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:40.155702+00:00
-- url     : https://prove2.me/submissions/6a50c830-ecfb-4c25-bd21-de10998e96c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : ∀ x : ℂ, x ^ 3 - 3 * x + 1 = 0 → x.im = 0) : ∀ x : ℂ, x ^ 3 - 3 * x + 1 = 0 → x ∈ Set.univ := by
  norm_num
