-- Prove2me | solution 1 for lean_workbook_plus_35687
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:52.620602+00:00
-- url     : https://prove2.me/submissions/d9b26ee6-6a22-45c0-8c08-0910502c8b02

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℂ) :
  x^12 + x^9 + x^6 + x^3 + 1 =
  x^2 * (x^10 - 1) + (x^4 + x) * (x^5 - 1) + x^4 + x^3 + x^2 + x + 1 := by
  (intros; ring)
