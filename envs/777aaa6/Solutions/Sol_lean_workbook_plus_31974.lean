-- Prove2me | solution 1 for lean_workbook_plus_31974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:43.915028+00:00
-- url     : https://prove2.me/submissions/035a694e-e064-419c-9664-53087e77602d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : 16 * a ^ 2 + 9 * b ^ 2 ≥ 24 * a * b := by
  intros
  
  have h_identity : (16 * a ^ 2 + 9 * b ^ 2) - (24 * a * b) = (16 : ℝ) * 1 * ((a + ((-3 / 4) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (16 * a ^ 2 + 9 * b ^ 2) - (24 * a * b) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
