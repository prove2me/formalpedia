-- Prove2me | solution 1 for lean_workbook_plus_16311
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:21.856693+00:00
-- url     : https://prove2.me/submissions/decfcb8c-0001-4d79-b459-f6a100b90f11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : -2 < x ∧ x < 3 ↔ -2 < x ∧ x < 3 := by
  norm_num
