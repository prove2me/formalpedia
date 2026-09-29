-- Prove2me | solution 1 for lean_workbook_plus_38421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:04.955667+00:00
-- url     : https://prove2.me/submissions/99758cf2-2dcb-43bc-8489-9e6cf7d53be5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^2 - b^2 = (a - b) * (a + b) := by
  (intros; linarith)
