-- Prove2me | solution 1 for lean_workbook_plus_8581
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:05.169485+00:00
-- url     : https://prove2.me/submissions/e2fa6688-4bb0-4bac-a74b-4e3fabb0dd72

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (18 / 17 + 6 * Real.sqrt 3 / 17) = (18 + 6 * Real.sqrt 3) / 17 := by
  (intros; linarith)
