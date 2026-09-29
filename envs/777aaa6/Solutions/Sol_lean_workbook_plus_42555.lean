-- Prove2me | solution 1 for lean_workbook_plus_42555
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:08.533936+00:00
-- url     : https://prove2.me/submissions/53d206bc-5468-499f-a965-4126a1dcea60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : b < c) (h₂ : b + c < a + 1) (h₃ : a > 1) : b < a := by
  (intros; linarith)
