-- Prove2me | solution 1 for lean_workbook_plus_9981
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:34.23561+00:00
-- url     : https://prove2.me/submissions/b53b69a9-4d9a-4d4c-8598-5ea29f700f4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : 7*x-3*y+0*z = 76) : 7*x-3*y = 76 := by
  (intros; simp_all)
