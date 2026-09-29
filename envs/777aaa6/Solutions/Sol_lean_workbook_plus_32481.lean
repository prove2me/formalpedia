-- Prove2me | solution 1 for lean_workbook_plus_32481
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:56:02.852877+00:00
-- url     : https://prove2.me/submissions/e9df992d-1eaf-4d38-8055-454621801f43

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^3 + b^3 = (a+b)*(a^2 - a*b + b^2) := by
  (intros; linarith)
