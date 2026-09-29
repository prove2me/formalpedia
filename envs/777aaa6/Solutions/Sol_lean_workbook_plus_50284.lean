-- Prove2me | solution 1 for lean_workbook_plus_50284
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:52.477151+00:00
-- url     : https://prove2.me/submissions/035419dc-7353-45dc-9e51-d7229cc0f8ac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^9 - 37*x^8 - 2*x^7 + 74*x^6 + x^4 - 37*x^3 - 2*x^2 + 74*x = x * (x^5 + 1) * (x^3 - 37*x^2 - 2*x + 74) := by
  (intros; linarith)
