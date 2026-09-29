-- Prove2me | solution 1 for lean_workbook_plus_39158
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:41.784369+00:00
-- url     : https://prove2.me/submissions/75c3b9b2-fd1c-4056-88c8-6adbb41b4a04

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (S a b : ℝ) : S = a * b * (a ^ 2 - b ^ 2) → S = a * b * (a + b) * (a - b) := by
  (intros; linarith)
