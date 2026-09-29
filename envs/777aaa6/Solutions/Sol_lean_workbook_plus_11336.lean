-- Prove2me | solution 1 for lean_workbook_plus_11336
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:03.02274+00:00
-- url     : https://prove2.me/submissions/297c50a6-0c5d-4004-8800-1b1b65d87af6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : 2 * p + 3 / 8 ≥ 3 / 4) :
  3 / 16 ≤ p := by
  (intros; linarith)
