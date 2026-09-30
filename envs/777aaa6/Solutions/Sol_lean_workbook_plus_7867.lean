-- Prove2me | solution 1 for lean_workbook_plus_7867
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:15.570598+00:00
-- url     : https://prove2.me/submissions/9c6799ed-8482-430b-b92e-0a824c823766

import Mathlib.Analysis.Complex.Basic

theorem solution (x_i x_j : ℝ) (h : x_i > x_j) :
  x_i * x_j * (x_i - x_j) < (x_i ^ 2 + x_i * x_j + x_j ^ 2) * (x_i - x_j) := by
  have hd : 0 < x_i - x_j := sub_pos.mpr h
  have hsq : 0 < x_i ^ 2 + x_j ^ 2 := by nlinarith [sq_pos_of_pos hd, sq_nonneg (x_i + x_j)]
  nlinarith [mul_pos hd hsq]
