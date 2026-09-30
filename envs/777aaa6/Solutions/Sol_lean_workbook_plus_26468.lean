-- Prove2me | solution 1 for lean_workbook_plus_26468
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:09.250896+00:00
-- url     : https://prove2.me/submissions/5f76a9e5-c015-4742-b5f7-c2681cc37ca7

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

lemma quotient_sqrt_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (a + b) ≤ Real.sqrt a := by
  apply (div_le_iff₀ (Real.sqrt_pos.2 (add_pos ha hb))).2
  calc
    a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt (le_of_lt ha)).symm
    _ ≤ Real.sqrt a * Real.sqrt (a + b) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg a)

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    a / Real.sqrt (a + b) + b / Real.sqrt (b + c) +
      c / Real.sqrt (c + d) + d / Real.sqrt (d + a) ≤
    Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
  linarith [quotient_sqrt_bound a b ha hb, quotient_sqrt_bound b c hb hc,
    quotient_sqrt_bound c d hc hd, quotient_sqrt_bound d a hd ha]
