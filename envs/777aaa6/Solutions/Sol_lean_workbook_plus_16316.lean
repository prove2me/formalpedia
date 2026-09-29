-- Prove2me | solution 1 for lean_workbook_plus_16316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:19.126109+00:00
-- url     : https://prove2.me/submissions/d9b7622f-71c4-4381-807c-2f6e4a054425

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x^2 + 4*x - 32 = 52 - 20) (h : x^2 + 4*x + 3 = 52 + 15) : (x^2 + 4*x - 32) / (x^2 + 4*x + 3) = (52 - 20) / (52 + 15) := by
  (intros; simp_all)
