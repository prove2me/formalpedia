-- Prove2me | solution 1 for lean_workbook_plus_1832
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:13.054729+00:00
-- url     : https://prove2.me/submissions/ebfae4ab-f5b0-4c57-a054-fc26b4cc6530

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x^2 - 18*x + 65 = 0) : (x-13)*(x-5) = 0 := by
  (intros; linarith)
