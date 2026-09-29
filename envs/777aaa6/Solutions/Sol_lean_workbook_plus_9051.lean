-- Prove2me | solution 1 for lean_workbook_plus_9051
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:03.923862+00:00
-- url     : https://prove2.me/submissions/80571587-f3d5-451e-8133-25e90b529f7c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ 1 / 3 * (a * b + b * c + c * a)^2 * (a + b + c)^2 := by
  intros
  
  have h_identity : ((a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2)) - (1 / 3 * (a * b + b * c + c * a)^2 * (a + b + c)^2) = ((2 / 3) : ℝ) * 1 * (((b * (a ^ 2)) + ((-1 / 2) * a * (c ^ 2)) + ((-1 / 2) * b * (c ^ 2)) + ((-1 / 2) * c * (b ^ 2)) + ((1 / 4) * a * (b ^ 2)) + ((1 / 4) * c * (a ^ 2))))^2 + ((5 / 8) : ℝ) * 1 * (((c * (a ^ 2)) + ((-3 / 5) * a * (b ^ 2)) + ((-2 / 5) * b * (c ^ 2)) + ((-2 / 5) * c * (b ^ 2)) + ((2 / 5) * a * (c ^ 2))))^2 + ((2 / 5) : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1 / 4) * a * (c ^ 2)) + ((1 / 4) * c * (b ^ 2))))^2 + ((3 / 8) : ℝ) * 1 * (((a * (c ^ 2)) + ((-1) * c * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2)) - (1 / 3 * (a * b + b * c + c * a)^2 * (a + b + c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
