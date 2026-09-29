-- Prove2me | solution 1 for lean_workbook_plus_35015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:14.692105+00:00
-- url     : https://prove2.me/submissions/25065f3b-1f95-4925-b3f5-64a2b3d7c7d8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
  set s := a+b+c
  set q := a*b+b*c+c*a
  have hs : 0 < s := by dsimp [s]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hsq : 0 ≤ s^2-3*q := by dsimp [s,q]; nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hi : 1+3/q-6/s = (q*(s-3)^2+3*(s^2-3*q))/(s^2*q) := by field_simp; ring
  have hp : 0 ≤ (q*(s-3)^2+3*(s^2-3*q))/(s^2*q) := by positivity
  change 1+3/q ≥ 6/s
  linarith
