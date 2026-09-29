-- Prove2me | solution 1 for lean_workbook_plus_58661
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:44.576573+00:00
-- url     : https://prove2.me/submissions/2508807b-ec14-4889-a79d-9a9bc25bbbf1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : 0 < p)
  (h₁ : p + (5 * p) / 6 + (25 * p) / 36 + (125 * p) / 216 = 1) :
  (p * (125 / 216)) = 125 / 671 := by
  (intros; linarith)
