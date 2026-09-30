-- Prove2me | solution 1 for lean_workbook_plus_65686
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:55.396094+00:00
-- url     : https://prove2.me/submissions/07bbd468-0eb1-4f8b-9685-8f319fe013b5

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b + c) ^ 3 >= (5 * a - b - c) * (5 * b - c - a) * (5 * c - a - b) := by
  obtain ⟨ha, hb, hc⟩ := hx
  nlinarith [mul_pos (sub_pos.2 hab) (sub_pos.2 hbc), mul_pos (sub_pos.2 hbc) (sub_pos.2 hca),
    mul_pos (sub_pos.2 hca) (sub_pos.2 hab),
    mul_pos (mul_pos (sub_pos.2 hab) (sub_pos.2 hbc)) (sub_pos.2 hca),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg (sub_pos.2 hab).le (sq_nonneg (a - b)),
    mul_nonneg (sub_pos.2 hbc).le (sq_nonneg (b - c)),
    mul_nonneg (sub_pos.2 hca).le (sq_nonneg (c - a)),
    mul_nonneg (sub_pos.2 hab).le (sq_nonneg (b - c)),
    mul_nonneg (sub_pos.2 hbc).le (sq_nonneg (c - a)),
    mul_nonneg (sub_pos.2 hca).le (sq_nonneg (a - b)),
    mul_nonneg (sub_pos.2 hab).le (sq_nonneg (c - a)),
    mul_nonneg (sub_pos.2 hbc).le (sq_nonneg (a - b)),
    mul_nonneg (sub_pos.2 hca).le (sq_nonneg (b - c))]
