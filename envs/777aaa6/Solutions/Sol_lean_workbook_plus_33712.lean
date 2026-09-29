-- Prove2me | solution 1 for lean_workbook_plus_33712
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:12.492642+00:00
-- url     : https://prove2.me/submissions/b8fe96a4-9060-4423-b65c-157564ac89d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = (1 - Real.sqrt 10) / 3) : x = (1 - Real.sqrt 10) / 3 := by
  (intros; simp_all)
