-- Prove2me | solution 1 for lean_workbook_plus_31156
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:14.004254+00:00
-- url     : https://prove2.me/submissions/b12a4d92-b855-40db-bf6c-7db46767a120

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℂ → ℂ) (h : 2 * f 0 = 0) : f 0 = 0 := by
  (intros; simp_all)
