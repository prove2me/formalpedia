-- Prove2me | solution 1 for lean_workbook_plus_60642
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:05.545062+00:00
-- url     : https://prove2.me/submissions/c0b0ce51-a9be-4234-a54c-7821f7d37eab

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (hab : 0 < a ∧ 0 < b) (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 4) : a / b + b / a + k * a * b / (a ^ 2 + b ^ 2) ≥ (k + 4) / 2 := by
  have ha : 0 < a := hab.1
  have hb : 0 < b := hab.2
  have hp : 0 < a*b := mul_pos hab.1 hab.2
  have ht : 0 < a^2+b^2 := by positivity
  have hf : 0 ≤ a^2+b^2-2*a*b := by nlinarith [sq_nonneg (a-b)]
  have hg : 0 ≤ 2*(a^2+b^2)-k*a*b := by
    have hkp := mul_nonneg (show 0 ≤ 4-k by linarith [hk.2]) hp.le
    nlinarith
  have hn := mul_nonneg hf hg
  have he : a/b+b/a+k*a*b/(a^2+b^2)-(k+4)/2 = ((a^2+b^2-2*a*b)*(2*(a^2+b^2)-k*a*b))/(2*a*b*(a^2+b^2)) := by
    field_simp [ne_of_gt hab.1, ne_of_gt hab.2, ne_of_gt ht]
    <;> ring
  have hd : 0 ≤ ((a^2+b^2-2*a*b)*(2*(a^2+b^2)-k*a*b))/(2*a*b*(a^2+b^2)) := div_nonneg hn (by positivity)
  linarith
