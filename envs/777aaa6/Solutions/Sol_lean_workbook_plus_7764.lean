-- Prove2me | solution 1 for lean_workbook_plus_7764
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:05.887607+00:00
-- url     : https://prove2.me/submissions/cf994556-85de-4041-ad5b-70eb6b58498b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e f : ℝ) (hab : a = 1) (hbc : b = 2) (hcd : c = 3) (hde : d = 3) (hef : e = 2) (haf : f = 1) : a + b + c + d + e + f = 12 := by
  (intros; linarith)
