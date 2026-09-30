-- Prove2me | solution 1 for lean_workbook_plus_82383
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:25.792218+00:00
-- url     : https://prove2.me/submissions/ab7ab27d-fa04-4f55-9047-6351546b207e

import Mathlib

theorem solution (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    1 ≥ a / b ↔ (x + a) / (x + b) ≥ a / b := by
  change a / b ≤ 1 ↔ a / b ≤ (x + a) / (x + b)
  rw [div_le_iff₀ hb, div_le_div_iff₀ hb (add_pos hx hb)]
  simp only [one_mul]
  constructor
  · intro h
    nlinarith [mul_nonneg (le_of_lt hx) (sub_nonneg.mpr h)]
  · intro h
    by_contra hba
    have hpos := mul_pos hx (sub_pos.mpr (lt_of_not_ge hba))
    nlinarith
