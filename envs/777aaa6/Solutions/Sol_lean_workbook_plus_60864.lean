-- Prove2me | solution 1 for lean_workbook_plus_60864
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:22:21.662606+00:00
-- url     : https://prove2.me/submissions/ac9742f3-f881-4a30-b51c-3b46c535e78f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h : a + b + c = 0) :
    (|a| + |b| + |c|) ^ 2 ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hab : -(a * b) ≤ |a| * |b| := by rw [← abs_mul]; exact neg_le_abs _
  have hbc : -(b * c) ≤ |b| * |c| := by rw [← abs_mul]; exact neg_le_abs _
  have hca : -(c * a) ≤ |c| * |a| := by rw [← abs_mul]; exact neg_le_abs _
  have hs : (a + b + c) ^ 2 = 0 := by rw [h]; ring
  nlinarith only [hs, hab, hbc, hca, sq_abs a, sq_abs b, sq_abs c]
