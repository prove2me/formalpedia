-- Prove2me | solution 1 for lean_workbook_plus_78737
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:54:55.771366+00:00
-- url     : https://prove2.me/submissions/1f224981-01ba-4ef8-911b-5451f1e8df8b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma three_mul_le_cubes (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : 3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  have h := mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
    (add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)))
      (sq_nonneg (c - a)))
  nlinarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a * b + b * c + c * a + a * b * c = 4) :
    a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 4 := by
  have h := three_mul_le_cubes a b c ha.le hb.le hc.le
  have h1 := three_mul_le_cubes a b 1 ha.le hb.le zero_le_one
  have h2 := three_mul_le_cubes b c 1 hb.le hc.le zero_le_one
  have h3 := three_mul_le_cubes c a 1 hc.le ha.le zero_le_one
  nlinarith

#print axioms solution
