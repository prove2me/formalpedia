-- Prove2me | solution 1 for lean_workbook_plus_19412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:10.824992+00:00
-- url     : https://prove2.me/submissions/deb47e96-ea45-4f2d-baa7-2b304b3713d1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (b c : ℝ)
  (h₀ : 2 * Real.sqrt 10 ≤ b + c) :
  (b^2 + 10) * (c^2 + 10) ≥ 10 * (b + c)^2 := by
  intros
  
  have h_identity : ((b^2 + 10) * (c^2 + 10)) - (10 * (b + c)^2) = (100 : ℝ) * 1 * ((1 + ((-1 / 10) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b^2 + 10) * (c^2 + 10)) - (10 * (b + c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
