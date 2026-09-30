-- Prove2me | solution 1 for lean_workbook_plus_32636
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:55:42.289638+00:00
-- url     : https://prove2.me/submissions/70d81a72-3541-4910-aed4-38c66e79ce1b

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :  Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 3   := by
  have small (u v w : ℝ) (hu : 0 < u ∧ u < 1)
      (hv : 0 < v ∧ v < 1) (hw : 0 < w ∧ w < 1) :
      Real.sqrt (u * v * w) < 1 := by
    have huv0 : 0 ≤ u * v := mul_nonneg hu.1.le hv.1.le
    have huv : u * v < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hu.1.le hu.2 hv.2.le
    have huvw : u * v * w < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left huv0 huv hw.2.le
    exact (Real.sqrt_lt' (by norm_num)).2 (by simpa only [one_pow] using huvw)
  have hleft := small a b c ha hb hc
  have hright := small (1 - a) (1 - b) (1 - c)
    (by constructor <;> linarith only [ha.1, ha.2])
    (by constructor <;> linarith only [hb.1, hb.2])
    (by constructor <;> linarith only [hc.1, hc.2])
  linarith only [hleft, hright]

#print axioms solution
