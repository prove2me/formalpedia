-- Prove2me | solution 1 for lean_workbook_plus_5420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:12:45.544477+00:00
-- url     : https://prove2.me/submissions/af682ee5-ece4-4fef-ae3c-632eb82ba925

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^5 + 2 * b^5) / (a^2 + 2 * b^2) + (a^4 + 2 * b^4) / (a + 2 * b) ≥ 2 / 3 * (a^3 + 2 * b^3) := by
  have hd1 : 0 < a^2+2*b^2 := by positivity
  have hd2 : 0 < a+2*b := by positivity
  have hn : 0 ≤ 2*(a-b)^2*(a^2+a*b+b^2)*(2*a^2+3*a*b+4*b^2) := by positivity
  have he : (a^5+2*b^5)/(a^2+2*b^2)+(a^4+2*b^4)/(a+2*b)-2/3*(a^3+2*b^3) = (2*(a-b)^2*(a^2+a*b+b^2)*(2*a^2+3*a*b+4*b^2))/(3*(a+2*b)*(a^2+2*b^2)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2]
    <;> ring
  have hp := div_nonneg hn (show 0 ≤ 3*(a+2*b)*(a^2+2*b^2) by positivity)
  linarith
