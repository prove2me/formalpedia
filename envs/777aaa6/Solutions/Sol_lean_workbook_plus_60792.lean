-- Prove2me | solution 1 for lean_workbook_plus_60792
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:53.156874+00:00
-- url     : https://prove2.me/submissions/a9d9a9a6-c64f-4752-8a4e-09a55f44c218

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z a b c : ℝ) : a = x + y ∧ b = y + z ∧ c = z + x → a + b + c = x + y + z + (x + y + z) := by
  (intros; linarith)
