-- Prove2me | solution 1 for lean_workbook_plus_29922
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:46.728305+00:00
-- url     : https://prove2.me/submissions/f44adda5-1fa6-498d-920f-8a44e26d8a6d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 3 / 8 = x / 24) :
  x = 9 := by
  (intros; linarith)
