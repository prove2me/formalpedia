-- Prove2me | solution 1 for lean_workbook_plus_19521
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:05.522449+00:00
-- url     : https://prove2.me/submissions/54b6b8b9-1a2d-4ddf-b1b3-b310d770776b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^4 * b^2 + a^2 * c^4 + b^4 * c^2 - b^3 * c * a^2 - c^3 * b^2 * a - a^3 * b * c^2) / (a^2 + a * b + b^2) / (b^2 + b * c + c^2) / (c^2 + c * a + a^2) ≥ 0 := by
  intros
  
  have h_identity : (((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((b ^ 4) * (c ^ 2)) + ((-1) * a * (b ^ 2) * (c ^ 3)) + ((-1) * b * (a ^ 3) * (c ^ 2)) + ((-1) * c * (a ^ 2) * (b ^ 3))) = (1 : ℝ) * 1 * (((b * (a ^ 2)) + ((-1 / 2) * a * (c ^ 2)) + ((-1 / 2) * c * (b ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * (((a * (c ^ 2)) + ((-1) * c * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((b ^ 4) * (c ^ 2)) + ((-1) * a * (b ^ 2) * (c ^ 3)) + ((-1) * b * (a ^ 3) * (c ^ 2)) + ((-1) * c * (a ^ 2) * (b ^ 3))) := by
    rw [h_identity]
    positivity
  have hn : 0 ≤ a^4*b^2+a^2*c^4+b^4*c^2-b^3*c*a^2-c^3*b^2*a-a^3*b*c^2 := by
    nlinarith only [h_nonnegative]
  have hab : 0 ≤ a^2+a*b+b^2 := by nlinarith only [sq_nonneg (a+b), sq_nonneg a, sq_nonneg b]
  have hbc : 0 ≤ b^2+b*c+c^2 := by nlinarith only [sq_nonneg (b+c), sq_nonneg b, sq_nonneg c]
  have hca : 0 ≤ c^2+c*a+a^2 := by nlinarith only [sq_nonneg (c+a), sq_nonneg c, sq_nonneg a]
  exact div_nonneg (div_nonneg (div_nonneg hn hab) hbc) hca
