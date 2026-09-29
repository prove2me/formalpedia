-- Prove2me | solution 1 for lean_workbook_plus_10132
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:28.813859+00:00
-- url     : https://prove2.me/submissions/d2425883-4825-4902-ac03-ffba5ad448be

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) : (c^2 * a^2 + b^2 * d^2 + (1 / 2) * (d^2 + b^2) * (c^2 + a^2) ≥ (a * b + c * d) * (b * c + a * d)) := by
  intros
  
  have h_identity : (c^2 * a^2 + b^2 * d^2 + (1 / 2) * (d^2 + b^2) * (c^2 + a^2)) - ((a * b + c * d) * (b * c + a * d)) = ((1 / 2) : ℝ) * 1 * (((a * b) + (c * d) + ((-1) * a * d) + ((-1) * b * c)))^2 + (1 : ℝ) * 1 * (((a * c) + ((-1) * b * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (c^2 * a^2 + b^2 * d^2 + (1 / 2) * (d^2 + b^2) * (c^2 + a^2)) - ((a * b + c * d) * (b * c + a * d)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
