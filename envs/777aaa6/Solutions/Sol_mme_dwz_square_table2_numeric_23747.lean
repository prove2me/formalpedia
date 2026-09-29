-- Prove2me | solution 1 for mme_dwz_square_table2_numeric_23747
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:17:49.720164+00:00
-- url     : https://prove2.me/submissions/ce834f82-c471-43bf-8885-b831b0c675ab

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_retained_log_rate_gt_157133
import Theorems.Thm_mme_dwz_square_component_log_rate_23747_gt_442868
import Mathlib.Analysis.Complex.ExponentialBounds

open MME.DWZSquare

private theorem two_rpow_600001_gt_640001 :
    (640001 / 10000 : ℝ) < (2 : ℝ) ^ (600001 / 100000 : ℝ) := by
  rw [show (600001 / 100000 : ℝ) = 6 + 1 / 100000 by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp := Real.add_one_le_exp (Real.log 2 * (1 / 100000 : ℝ))
  have hlog := Real.log_two_gt_d9
  nlinarith

theorem solution :
    (640001 / 10000 : ℝ) < squareRate (23747 / 30000) := by
  have hret := mme_dwz_square_retained_log_rate_gt_157133
  have hcomp := mme_dwz_square_component_log_rate_23747_gt_442868
  have hsum :
      (600001 / 100000 : ℝ) <
        retainedLogRate + componentLogRate (23747 / 30000) := by
    nlinarith
  have hmono :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hsum
  rw [squareRate, Real.rpow_eq_pow]
  exact two_rpow_600001_gt_640001.trans hmono

