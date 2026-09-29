-- Prove2me | solution 1 for lean_workbook_plus_25615
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:38.428319+00:00
-- url     : https://prove2.me/submissions/dd754fc6-8128-4545-aa8f-1ce098ddeaeb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z =
    1 / 2 * (x + y + z) * ((x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2) := by
  (intros; linarith)
