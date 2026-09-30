-- Prove2me | solution 1 for lean_workbook_plus_81806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:20:32.232365+00:00
-- url     : https://prove2.me/submissions/de35ba70-bc1d-4708-9d07-bc379041e6d8

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) :
    a * b + b * c + c * a ≥ 3 := by
  have hab := mul_nonneg ha.le hb.le
  have hbc := mul_nonneg hb.le hc.le
  have hca := mul_nonneg hc.le ha.le
  have hprod : (a * b) * (b * c) * (c * a) = 1 := by
    calc
      _ = (a * b * c) ^ 2 := by ring
      _ = 1 := by rw [habc]; norm_num
  have hm := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hab hbc hca (by norm_num)
  rw [← Real.mul_rpow hab hbc, ← Real.mul_rpow (mul_nonneg hab hbc) hca,
    hprod, Real.one_rpow] at hm
  linarith

#print axioms solution
