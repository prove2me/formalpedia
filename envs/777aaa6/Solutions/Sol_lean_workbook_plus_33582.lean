-- Prove2me | solution 1 for lean_workbook_plus_33582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:21.535817+00:00
-- url     : https://prove2.me/submissions/61d374d0-0ecc-42f3-8ada-cce0edcfdece

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b c : ℝ) : (∃ x, x^2 + b * x + c = 0) ↔ b^2 - 4*c >= 0 := by
  constructor
  · rintro ⟨x,hx⟩
    nlinarith [sq_nonneg (2*x+b)]
  · intro h
    refine ⟨(-b+Real.sqrt (b^2-4*c))/2, ?_⟩
    have hs := Real.sq_sqrt h
    nlinarith
