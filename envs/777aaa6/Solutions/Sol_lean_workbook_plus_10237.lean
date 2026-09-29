-- Prove2me | solution 1 for lean_workbook_plus_10237
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:35.023058+00:00
-- url     : https://prove2.me/submissions/33ab900b-f578-4a11-abd7-f373548d64b2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) (h : 0 < k) :
  ((2 * k - 1 : ℝ) / (2 * k) : ℝ) ≤ Real.sqrt ((2 * k - 1 : ℝ) / (2 * k + 1 : ℝ)) := by
  have hk : (1:ℝ) ≤ k := by exact_mod_cast h
  have hp : 0 < (k:ℝ) := by linarith
  have hi : (2*(k:ℝ)-1)/(2*(k:ℝ)+1)-((2*(k:ℝ)-1)/(2*(k:ℝ)))^2 = (2*(k:ℝ)-1)/(4*(k:ℝ)^2*(2*(k:ℝ)+1)) := by field_simp; ring
  have hh : 0 ≤ (2*(k:ℝ)-1)/(4*(k:ℝ)^2*(2*(k:ℝ)+1)) := div_nonneg (by linarith) (by positivity)
  apply Real.le_sqrt_of_sq_le
  linarith
