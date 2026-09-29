-- Prove2me | solution 1 for lean_workbook_plus_43244
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:04.320003+00:00
-- url     : https://prove2.me/submissions/2f30bd2c-4bb5-4310-8b56-c19647c8184c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (hab : a + b = c + d) (hab' : a + b ≠ 0) : (a + b) ^ 3 = (c + d) ^ 3 := by
  (intros; simp_all)
