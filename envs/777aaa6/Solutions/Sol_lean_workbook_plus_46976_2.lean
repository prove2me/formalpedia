-- Prove2me | solution 2 for lean_workbook_plus_46976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:43.455994+00:00
-- url     : https://prove2.me/submissions/22dff045-f052-4d40-8f38-9f68a628536a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (h1 : a >= 1 ∧ b >= 1 ∧ c >= 1): a + b + c >= 3 := by
  (intros; linarith)
