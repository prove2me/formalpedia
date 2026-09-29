-- Prove2me | solution 1 for lean_workbook_plus_25978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:11.693597+00:00
-- url     : https://prove2.me/submissions/7ba62764-c658-46d3-afea-813ccab0d79b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) : m / (1 + m + m * n) + n / (1 + n + n * p) + p / (1 + p + p * m) ≤ 1 := by
  intros
  
  have h_identity : (1 + ((m ^ 2) * (n ^ 2) * (p ^ 2)) + ((-2) * m * n * p)) = (1 : ℝ) * 1 * ((1 + ((-1) * m * n * p)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((m ^ 2) * (n ^ 2) * (p ^ 2)) + ((-2) * m * n * p)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + m + (m * n)) * (1 + n + (n * p)) * (1 + p + (m * p))) := by positivity
  have h_rational : (1) - (m / (1 + m + m * n) + n / (1 + n + n * p) + p / (1 + p + p * m)) = ((1 + ((m ^ 2) * (n ^ 2) * (p ^ 2)) + ((-2) * m * n * p))) / (((1 + m + (m * n)) * (1 + n + (n * p)) * (1 + p + (m * p)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
