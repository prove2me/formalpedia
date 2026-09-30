-- Prove2me | solution 2 for lean_workbook_plus_42269
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:36.54976+00:00
-- url     : https://prove2.me/submissions/e5838236-e919-4db6-8731-b793fc45e61a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x = 100)
  (h₁ : (1 - 0.3) * (1 - 0.2) = 0.56) :
  x * (1 - 0.3) * (1 - 0.2) = 56 := by
  (intros; linarith)
