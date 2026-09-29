-- Prove2me | solution 1 for lean_workbook_plus_61957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:20:02.114676+00:00
-- url     : https://prove2.me/submissions/3b0edae1-5d67-45f1-9679-4c51597c74c4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ x, (x - 1) * (x - 2) * (x - 4) * (x - 5) ≥ (-9 / 4) := by
  have sourceClaim (r : ℝ) : (-9/4 : ℝ) ≤ (r-1)*(r-2)*(r-4)*(r-5) := by
    nlinarith only [sq_nonneg ((r-3)^2-(5/2 : ℝ))]
  intro x
  change (-3 : ℤ) ≤ (x-1)*(x-2)*(x-4)*(x-5)
  have hr : (-3 : ℝ) ≤ ((x:ℝ)-1)*((x:ℝ)-2)*((x:ℝ)-4)*((x:ℝ)-5) := by
    linarith [sourceClaim (x:ℝ)]
  exact_mod_cast hr
