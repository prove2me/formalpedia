-- Prove2me | solution 1 for lean_workbook_plus_36616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:22.625496+00:00
-- url     : https://prove2.me/submissions/8071c949-bda9-48a5-949b-0a13e0e2155f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 2 * (2 * (2 * (2 * x))) = 48) : x = 3 := by
  (intros; linarith)
