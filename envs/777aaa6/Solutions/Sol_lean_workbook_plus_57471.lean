-- Prove2me | solution 1 for lean_workbook_plus_57471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:03:14.341135+00:00
-- url     : https://prove2.me/submissions/66b7dd96-6f17-432c-90b3-3f6926ae53f3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem triple_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3*a*b*c ≤ a^3+b^3+c^3 := by
  have hp := mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
    (add_nonneg (add_nonneg (sq_nonneg (a-b)) (sq_nonneg (b-c)))
      (sq_nonneg (c-a)))
  nlinarith only [hp]

theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hd : d ≥ 0) : a^3+b^3+c^3+d^3 ≥ a*b*c+b*c*d+c*d*a+d*a*b := by
  nlinarith only [triple_bound a b c ha hb hc, triple_bound b c d hb hc hd,
    triple_bound c d a hc hd ha, triple_bound d a b hd ha hb]
