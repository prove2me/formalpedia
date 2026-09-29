-- Prove2me | solution 1 for lean_workbook_plus_63099
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:47.548557+00:00
-- url     : https://prove2.me/submissions/b6acea84-b076-4693-9c3b-a7a1f7b26f76

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c : ℝ) : c^2 = 1 ↔ c = 1 ∨ c = -1 := by
  norm_num
