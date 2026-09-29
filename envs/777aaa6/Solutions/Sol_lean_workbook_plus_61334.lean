-- Prove2me | solution 1 for lean_workbook_plus_61334
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:06.124345+00:00
-- url     : https://prove2.me/submissions/2558ac48-b1f5-47df-a7b0-628e7be9d046

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (3*x = 4*y) → (y = 3/4 * x) := by
  (intros; linarith)
