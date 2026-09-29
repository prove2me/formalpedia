-- Prove2me | solution 1 for lean_workbook_plus_61509
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:47.213882+00:00
-- url     : https://prove2.me/submissions/0a938b0f-1d1a-4284-9578-5b34bd97f8f7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (q e : ℚ)
  (h₀ : q = 1 / 3)
  (h₁ : e = 17 / 27) :
  q + e = 26 / 27 := by
  (intros; linarith)
