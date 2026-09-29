-- Prove2me | solution 1 for lean_workbook_plus_70618
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:21.779796+00:00
-- url     : https://prove2.me/submissions/00282a87-dbe6-4870-b725-437f35fc4e5b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2 := by
  (intros; linarith)
