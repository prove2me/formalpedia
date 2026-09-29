-- Prove2me | solution 1 for lean_workbook_plus_62013
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:36.023864+00:00
-- url     : https://prove2.me/submissions/b280ea64-a0ed-4fb0-9a1a-e5ef3c767e93

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b + c = 18) (h2 : a^2 + b^2 + c^2 - a * b - b * c - c * a = 18) : a^2 + b^2 + c^2 - a * b - b * c - c * a = 18 := by
  (intros; simp_all)
