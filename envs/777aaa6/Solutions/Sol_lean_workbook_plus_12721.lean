-- Prove2me | solution 1 for lean_workbook_plus_12721
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:06.666985+00:00
-- url     : https://prove2.me/submissions/1eb75b08-4369-47a4-94ef-bff5914d8249

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x - y) ^ 4 + (y - z) ^ 4 + (z - x) ^ 4 =
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) ^ 2 := by
  (intros; linarith)
