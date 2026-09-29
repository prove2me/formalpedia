-- Prove2me | solution 1 for lean_workbook_plus_25216
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:02.198202+00:00
-- url     : https://prove2.me/submissions/9d78a14c-e6f8-4e08-991a-72cc871d1e6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x1 y1 x2 y2 : ℝ) :
  Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = Real.sqrt ((y2 - y1)^2 + (x2 - x1)^2) := by
  (intros; ring)
