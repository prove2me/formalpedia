-- Prove2me | solution 1 for lean_workbook_plus_25262
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:05.262886+00:00
-- url     : https://prove2.me/submissions/73ae5eb7-090c-441d-8048-4e614cc46286

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c: ℝ) : (2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 ≥ 3 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4)) := by
  intros
  
  have h_identity : ((2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2) - (3 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4))) = (4 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + (3 : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2) - (3 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4))) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
