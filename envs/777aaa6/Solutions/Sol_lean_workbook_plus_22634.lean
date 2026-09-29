-- Prove2me | solution 1 for lean_workbook_plus_22634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:33.290061+00:00
-- url     : https://prove2.me/submissions/16176a36-0423-44b9-be3c-162e3477131c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y1 y2 : ℝ) (hy1 : y1 ≠ y2) (h1 : y1^3 - y1 / 4 = y2^3 - y2 / 4) : y1^3 - y2^3 = y1 / 4 - y2 / 4 := by
  (intros; linarith)
