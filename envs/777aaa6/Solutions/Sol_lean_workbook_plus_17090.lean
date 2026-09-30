-- Prove2me | solution 1 for lean_workbook_plus_17090
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:35.455269+00:00
-- url     : https://prove2.me/submissions/a1a4fb4b-d91b-4e11-9299-55b0edce2e03

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a)
    (hca : a + c > b) :
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  obtain ⟨ha, hb, hc⟩ := hx
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
    rcases le_total a c with h3 | h3 <;>
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) hc.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)) hb.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)) ha.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) ha.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)) hc.le,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)) hb.le,
      mul_nonneg (sq_nonneg (a - b)) (sub_pos.2 hab).le,
      mul_nonneg (sq_nonneg (b - c)) (sub_pos.2 hbc).le,
      mul_nonneg (sq_nonneg (a - c)) (sub_pos.2 hca).le]
