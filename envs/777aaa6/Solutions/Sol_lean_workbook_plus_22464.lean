-- Prove2me | solution 1 for lean_workbook_plus_22464
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:35.339168+00:00
-- url     : https://prove2.me/submissions/3ad71c4a-ec51-4a49-8d12-d64e2ba91bfd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z w : ℝ) (h₁ : x + 5*y - 3*z + 6*w = 13) (h₂ : 2*x + 8*y - 2*z + w = 42) (h₃ : 3*x - 7*y + 11*z - w = 23) : w + x + y + z = 13 := by
  (intros; linarith)
