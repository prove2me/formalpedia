-- Prove2me | solution 1 for lean_workbook_plus_32906
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:21:55.039357+00:00
-- url     : https://prove2.me/submissions/f523a61b-2c90-4b50-84d1-17162d5637d4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 1 / a + 1 / b + 1 / c + 1 / d) : a * b + a * c + a * d + b * c + b * d + c * d ≥ 6 * a * b * c * d   := by
  let s := a + b + c + d
  let p := a*b+a*c+a*d+b*c+b*d+c*d
  let t := a*b*c+a*b*d+a*c*d+b*c*d
  let q := a*b*c*d
  have hs : 0 < s := by dsimp [s]; positivity
  have he : s * q = t := by
    dsimp [s, q, t]
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hd] at hab
    nlinarith only [hab]
  have hnewton : 6 * t ≤ s * p := by
    dsimp [s, p, t]
    nlinarith [mul_nonneg (sq_nonneg (a-b)) (show 0 ≤ c+d by positivity), mul_nonneg (sq_nonneg (a-c)) (show 0 ≤ b+d by positivity), mul_nonneg (sq_nonneg (a-d)) (show 0 ≤ b+c by positivity), mul_nonneg (sq_nonneg (b-c)) (show 0 ≤ a+d by positivity), mul_nonneg (sq_nonneg (b-d)) (show 0 ≤ a+c by positivity), mul_nonneg (sq_nonneg (c-d)) (show 0 ≤ a+b by positivity)]
  suffices hh : p ≥ 6 * q by
    dsimp [p, q] at hh
    nlinarith only [hh]
  by_contra hbad
  have hn : s * (p - 6 * q) < 0 := mul_neg_of_pos_of_neg hs (by linarith)
  nlinarith only [he, hnewton, hn]
