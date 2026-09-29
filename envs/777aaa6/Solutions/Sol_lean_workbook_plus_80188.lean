-- Prove2me | solution 1 for lean_workbook_plus_80188
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:38.250598+00:00
-- url     : https://prove2.me/submissions/d9b891c8-43f7-40e7-9066-5575d0dad447

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 ≥ 0 := by
  (intros; positivity)
