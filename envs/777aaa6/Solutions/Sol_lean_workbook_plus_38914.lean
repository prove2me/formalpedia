-- Prove2me | solution 1 for lean_workbook_plus_38914
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:12.608806+00:00
-- url     : https://prove2.me/submissions/1c0643da-7e6e-44b4-85c0-816a45ba4e63

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) / 2 = (b + a) / 2 := by
  (intros; linarith)
