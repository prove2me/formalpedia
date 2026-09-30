-- Prove2me | solution 1 for lean_workbook_plus_26009
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:19.576692+00:00
-- url     : https://prove2.me/submissions/2fe9bdb3-a1c4-448b-9c92-27e76877b7b1

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 := by
  have hab : 0 < a + b := by linarith
  have hbc : 0 < b + c := by linarith
  rw [ge_iff_le, div_add_div _ _ hb.ne' hc.ne', div_add_div _ _ (by positivity) ha.ne',
    div_add_div _ _ hbc.ne' hab.ne', div_add_one (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos ha ha) hb, mul_pos (mul_pos ha ha) hc,
    mul_pos (mul_pos hb hb) ha, mul_pos (mul_pos hb hb) hc, mul_pos (mul_pos hc hc) ha,
    mul_pos (mul_pos hc hc) hb, mul_pos (mul_pos ha ha) ha, mul_pos (mul_pos hb hb) hb,
    mul_pos (mul_pos hc hc) hc]
