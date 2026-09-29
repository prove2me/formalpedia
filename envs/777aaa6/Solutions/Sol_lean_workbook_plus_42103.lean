-- Prove2me | solution 1 for lean_workbook_plus_42103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:46.657877+00:00
-- url     : https://prove2.me/submissions/e1a57e47-1169-498a-bdd6-9a1bcbf9b157

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r b : ℚ)
  (h₀ : 0 < r ∧ 0 < b)
  (h₁ : r = 2 * b)
  (h₂ : (2 * r / 7 + 5 * b / 7) = 1 / 6) :
  r = 7 / 27 := by
  (intros; linarith)
