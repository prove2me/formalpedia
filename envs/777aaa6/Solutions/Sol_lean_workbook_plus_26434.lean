-- Prove2me | solution 1 for lean_workbook_plus_26434
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:13.094777+00:00
-- url     : https://prove2.me/submissions/652df2ef-7172-4c42-babf-9a56ea663a8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : a * b + b * c + c * a = (a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b) - (a + b + c) ^ 2 := by
  (intros; linarith)
