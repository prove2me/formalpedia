-- Prove2me | solution 1 for lean_workbook_plus_36969
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:52.067721+00:00
-- url     : https://prove2.me/submissions/5e2c2564-4115-4490-90ca-39eb0d2d8b8c

import Mathlib.Analysis.Complex.Basic

theorem solution : (2179 + 301 * Real.sqrt 301) / 6480 < 71 / 40 := by
  have h : Real.sqrt 301 < 18 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h2 : 301 * Real.sqrt 301 < 301 * 18 := by
    exact mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (2179 + 301 * Real.sqrt 301) / 6480 < (2179 + 301 * 18) / 6480 := by
    apply div_lt_div_of_pos_right _ (by norm_num)
    linarith
  calc (2179 + 301 * Real.sqrt 301) / 6480 < (2179 + 301 * 18) / 6480 := h3
    _ < 71 / 40 := by norm_num
