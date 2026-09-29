-- Prove2me | solution 1 for lean_workbook_plus_10938
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:29.950778+00:00
-- url     : https://prove2.me/submissions/5f89af79-f411-4f33-a24e-0328dca0610c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) = 1 / 2 * ((a - b)^2 + (a - c)^2 + (b - c)^2) := by
  (intros; linarith)
