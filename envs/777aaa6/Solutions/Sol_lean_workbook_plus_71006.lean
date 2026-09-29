-- Prove2me | solution 1 for lean_workbook_plus_71006
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:11.641871+00:00
-- url     : https://prove2.me/submissions/b99c3134-582c-4f60-9340-49269ee9bb95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  ((a + 3 * b) ^ 2 * (a - 3 * b) ^ 2) ^ 2 = (a ^ 2 - 9 * b ^ 2) ^ 4 := by
  (intros; linarith)
