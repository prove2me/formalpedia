-- Prove2me | solution 1 for lean_workbook_plus_22621
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:08.758339+00:00
-- url     : https://prove2.me/submissions/cb48ddca-110e-4dc6-92f2-68f186885faf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) (h : x + 17 = 12) : x = -5 := by
  (intros; omega)
