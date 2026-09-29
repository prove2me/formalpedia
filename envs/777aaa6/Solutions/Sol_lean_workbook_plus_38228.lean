-- Prove2me | solution 1 for lean_workbook_plus_38228
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:29.354759+00:00
-- url     : https://prove2.me/submissions/dd49293e-31e0-49a1-bfa4-5ec6ac49ea71

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 10 * x ^ 3 - 39 * x ^ 2 + 29 * x - 6 = (x - 3) * (2 * x - 1) * (5 * x - 2) := by
  (intros; linarith)
