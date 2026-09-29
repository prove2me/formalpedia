-- Prove2me | solution 1 for lean_workbook_plus_61499
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:50.738311+00:00
-- url     : https://prove2.me/submissions/89a1d9d2-285d-4860-a1db-4eb6541c712f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (q e : ℚ)
  (h₀ : q = 3 / 4)
  (h₁ : e = 7 / 4) :
  q + e = 5 / 2 := by
  (intros; linarith)
