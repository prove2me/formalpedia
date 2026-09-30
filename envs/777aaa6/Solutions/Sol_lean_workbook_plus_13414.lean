-- Prove2me | solution 1 for lean_workbook_plus_13414
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:03.188469+00:00
-- url     : https://prove2.me/submissions/90dad06f-c7d2-44ad-a1ca-4b25ef07e5ca

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h : x*y ≥ 1) : (x^2 + 1)^(-1:ℤ) + (y^2 + 1)^(-1:ℤ) ≥ 2/(1 + x*y) := by
  simp only [zpow_neg, zpow_one]
  have hx : 0 < x ^ 2 + 1 := by positivity
  have hy : 0 < y ^ 2 + 1 := by positivity
  have hxy : 0 < 1 + x * y := by linarith
  rw [ge_iff_le, inv_eq_one_div, inv_eq_one_div, div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ hxy (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (x - y)), sq_nonneg (x - y), sq_nonneg (x*y - 1)]
