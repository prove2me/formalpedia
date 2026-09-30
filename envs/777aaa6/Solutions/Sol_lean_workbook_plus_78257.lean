-- Prove2me | solution 1 for lean_workbook_plus_78257
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:58.149614+00:00
-- url     : https://prove2.me/submissions/5630518d-392f-4d99-9837-d801b5d476bf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (ha : 0 < a ∧ 0 < b ∧ 0 < c)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c)
      ≤ 3 * a * b * c := by
  nlinarith only [
    mul_nonneg (sub_nonneg.mpr hab.le) (sq_nonneg (a - b)),
    mul_nonneg (sub_nonneg.mpr hbc.le) (sq_nonneg (b - c)),
    mul_nonneg (sub_nonneg.mpr hca.le) (sq_nonneg (c - a))]
