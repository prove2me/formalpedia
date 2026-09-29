-- Prove2me | solution 1 for lean_workbook_plus_24266
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:07:08.479523+00:00
-- url     : https://prove2.me/submissions/968da877-f2ac-4bc2-8813-25636dd898fa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a * b / (a + 2 * b + c) + b * c / (b + 2 * c + a) + c * a / (c + 2 * a + b)) ≤ 1 / 4 * (a + b + c) := by
  have hD : 0 < 4*(a+2*b+c)*(b+2*c+a)*(c+2*a+b) := by positivity
  have hidentity :
      (1/4*(a+b+c) - (a*b/(a+2*b+c) + b*c/(b+2*c+a) + c*a/(c+2*a+b))) *
        (4*(a+2*b+c)*(b+2*c+a)*(c+2*a+b)) =
      2*(a^2-b*c)^2 + (a*b-a*c)^2 + (a*b-b*c)^2 + 2*(a*b-c^2)^2 + 2*(a*c-b^2)^2 + (a*c-b*c)^2 + (b*c)*(4*(a-c)^2+(b-c)^2) + (a*c)*(4*(a-b)^2+(a-c)^2) + (a*b)*((a-b)^2+4*(b-c)^2) := by
    field_simp
    <;> ring
  have hsum : 0 ≤ 2*(a^2-b*c)^2 + (a*b-a*c)^2 + (a*b-b*c)^2 + 2*(a*b-c^2)^2 + 2*(a*c-b^2)^2 + (a*c-b*c)^2 + (b*c)*(4*(a-c)^2+(b-c)^2) + (a*c)*(4*(a-b)^2+(a-c)^2) + (a*b)*((a-b)^2+4*(b-c)^2) := by positivity
  have hproduct : 0 ≤
      (1/4*(a+b+c) - (a*b/(a+2*b+c) + b*c/(b+2*c+a) + c*a/(c+2*a+b))) *
        (4*(a+2*b+c)*(b+2*c+a)*(c+2*a+b)) := by rw [hidentity]; exact hsum
  have hgap := nonneg_of_mul_nonneg_left hproduct hD
  linarith only [hgap]
