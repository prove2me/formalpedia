-- Prove2me | solution 1 for lean_workbook_plus_66634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:05.825352+00:00
-- url     : https://prove2.me/submissions/1556a72c-3cef-43c1-9412-b9b8d01e9c1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t x : ℝ) (ht : t = 10) (hx : x = Real.sqrt (623/6)) : t = 10 ∧ x = Real.sqrt (623/6) := by
  (intros; simp_all)
