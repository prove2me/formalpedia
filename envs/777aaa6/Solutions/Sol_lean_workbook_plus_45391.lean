-- Prove2me | solution 1 for lean_workbook_plus_45391
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:39.665585+00:00
-- url     : https://prove2.me/submissions/f60866b8-349c-45cd-a84f-2a800ddecaa3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a^2 + b^2 = c^2 + d^2) : (a - c) * (a + c) = (d - b) * (d + b) := by
  (intros; linarith)
