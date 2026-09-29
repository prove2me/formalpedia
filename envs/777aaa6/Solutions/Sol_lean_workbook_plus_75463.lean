-- Prove2me | solution 1 for lean_workbook_plus_75463
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:42.464116+00:00
-- url     : https://prove2.me/submissions/9ba28688-3740-4f3c-924b-a785fab60259

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 5 / 8 - 1 / 4 = 0.375) : 5 / 8 - 1 / 4 = 0.375 := by
  (intros; simp_all)
