-- Prove2me | solution 1 for lean_workbook_plus_16976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:19.617835+00:00
-- url     : https://prove2.me/submissions/dab92b14-9a72-41d9-939e-3eb3c395f6a3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :  (a + 2 * b + c) * (a + b + c) ^ 2 ≥ 4 * (a + b) * (b + c) * (c + a) + b ^ 2 * (a + 2 * b + c) + (c + a) * (a - c) ^ 2 := by
  (intros; linarith)
