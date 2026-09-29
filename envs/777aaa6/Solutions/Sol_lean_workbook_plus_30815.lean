-- Prove2me | solution 1 for lean_workbook_plus_30815
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:33.360745+00:00
-- url     : https://prove2.me/submissions/06409adb-d7f8-4850-a5b1-9de477dffcfe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - b*c - c*a) := by
  (intros; linarith)
