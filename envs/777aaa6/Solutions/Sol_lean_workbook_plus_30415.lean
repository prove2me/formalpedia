-- Prove2me | solution 1 for lean_workbook_plus_30415
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:00.207969+00:00
-- url     : https://prove2.me/submissions/728629f0-973b-4301-a4f7-98b629602f5d

import Mathlib.Analysis.Complex.Basic

/-- The inequality in the ordered case `c ≤ b ≤ a`. -/
lemma key_30415 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : b ≤ a) (hbc : c ≤ b) :
    (a^3 + b^3 + c^3) / 3 ≥ a * b * c + (3 / 4) * |(a - b) * (b - c) * (c - a)| := by
  have hx : 0 ≤ a - b := sub_nonneg.mpr hab
  have hy : 0 ≤ b - c := sub_nonneg.mpr hbc
  have hz : c - a ≤ 0 := sub_nonpos.mpr (hbc.trans hab)
  have hp : (a - b) * (b - c) * (c - a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx hy) hz
  rw [abs_of_nonpos hp]
  nlinarith [mul_nonneg hc.le (sq_nonneg (a - b)), mul_nonneg hc.le (sq_nonneg (b - c)),
    mul_nonneg hc.le (mul_nonneg hx hy), mul_nonneg hx (sq_nonneg (a - b)),
    mul_nonneg hx (mul_nonneg hx hy), mul_nonneg hy (mul_nonneg hx hy),
    mul_nonneg hy (sq_nonneg (b - c))]

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^3 + b^3 + c^3) / 3 ≥ a * b * c + (3 / 4) * |(a - b) * (b - c) * (c - a)| := by
  rcases le_total b a with hab | hab <;> rcases le_total c b with hbc | hbc <;>
    rcases le_total c a with hac | hac
  · exact key_30415 a b c ha hb hc hab hbc
  · exact key_30415 a b c ha hb hc hab hbc
  · -- b ≤ a, b ≤ c, c ≤ a : order a ≥ c ≥ b
    have := key_30415 a c b ha hc hb hac hbc
    rw [show (a - c) * (c - b) * (b - a) = -((a - b) * (b - c) * (c - a)) by ring, abs_neg] at this
    linarith
  · -- b ≤ a, b ≤ c, a ≤ c : order c ≥ a ≥ b
    have := key_30415 c a b hc ha hb hac hab
    rw [show (c - a) * (a - b) * (b - c) = (a - b) * (b - c) * (c - a) by ring] at this
    linarith
  · -- a ≤ b, c ≤ b, c ≤ a : order b ≥ a ≥ c
    have := key_30415 b a c hb ha hc hab hac
    rw [show (b - a) * (a - c) * (c - b) = -((a - b) * (b - c) * (c - a)) by ring, abs_neg] at this
    linarith
  · -- a ≤ b, c ≤ b, a ≤ c : order b ≥ c ≥ a
    have := key_30415 b c a hb hc ha hbc hac
    rw [show (b - c) * (c - a) * (a - b) = (a - b) * (b - c) * (c - a) by ring] at this
    linarith
  · -- a ≤ b, b ≤ c, c ≤ a : all equal-ish; order c ≥ b ≥ a
    have := key_30415 c b a hc hb ha hbc hab
    rw [show (c - b) * (b - a) * (a - c) = -((a - b) * (b - c) * (c - a)) by ring, abs_neg] at this
    linarith
  · -- a ≤ b, b ≤ c, a ≤ c : order c ≥ b ≥ a
    have := key_30415 c b a hc hb ha hbc hab
    rw [show (c - b) * (b - a) * (a - c) = -((a - b) * (b - c) * (c - a)) by ring, abs_neg] at this
    linarith
