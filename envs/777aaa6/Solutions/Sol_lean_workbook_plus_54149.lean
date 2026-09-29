-- Prove2me | solution 1 for lean_workbook_plus_54149
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:12.694685+00:00
-- url     : https://prove2.me/submissions/3c8cec42-2fc4-4b5e-bc8d-2e051d8218bf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : (x - 9) / 3 = 43) :
  (x - 3) / 9 = 15 := by
  (intros; linarith)
