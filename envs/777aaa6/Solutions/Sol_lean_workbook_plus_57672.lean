-- Prove2me | solution 1 for lean_workbook_plus_57672
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:18.958727+00:00
-- url     : https://prove2.me/submissions/42f29cf1-e216-4cca-a9fa-295f39807659

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (b d c : ℝ) :
  (b * d + c) * (d * c + b) ≤ (1 / 4) * (d + 1)^2 * (b + c)^2 := by
  intros
  
  have h_identity : ((1 / 4) * (d + 1)^2 * (b + c)^2) - ((b * d + c) * (d * c + b)) = ((1 / 4) : ℝ) * 1 * ((b + ((-1) * c) + (c * d) + ((-1) * b * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((1 / 4) * (d + 1)^2 * (b + c)^2) - ((b * d + c) * (d * c + b)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
