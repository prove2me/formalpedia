-- Prove2me | solution 1 for lean_workbook_plus_11826
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:49:21.349022+00:00
-- url     : https://prove2.me/submissions/dccdeccd-bcc5-4ae3-a74f-3f889a274eaa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a / (a + 2 * b + 1) + b / (b + 2 * a + 1) = 1 / 2) : a ^ 3 + b ^ 3 ≤ 2 := by
  have hd₁ : 0 < a+2*b+1 := by positivity
  have hd₂ : 0 < b+2*a+1 := by positivity
  have hpoly : 2*a^2+2*b^2-a*b-a-b-1=0 := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂] at hab
    nlinarith only [hab]
  have hs : a+b ≤ 2 := by nlinarith only [hpoly, sq_nonneg (a-b), ha, hb]
  have hs2 : 0 ≤ 2-a-b := by linarith
  have ht : 0 ≤ 5+(a+b)-(a+b)^2 := by
    nlinarith only [mul_nonneg hs2 (show 0 ≤ a+b+1 by positivity)]
  have hprod := mul_nonneg hs2 ht
  have hmul := congrArg (fun t : ℝ => t*(a+b)) hpoly
  nlinarith only [hprod,hmul]
