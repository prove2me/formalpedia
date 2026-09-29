-- Prove2me | solution 1 for lean_workbook_plus_38267
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:51:48.07184+00:00
-- url     : https://prove2.me/submissions/3130a7fa-3d6e-4912-866d-f700a3188619

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = 1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by
  (intros; linarith)
