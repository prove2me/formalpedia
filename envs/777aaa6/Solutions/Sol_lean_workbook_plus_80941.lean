-- Prove2me | solution 1 for lean_workbook_plus_80941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:54.531375+00:00
-- url     : https://prove2.me/submissions/7ec3a28c-3258-487c-8b5e-97671189c311

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (x y : ℝ) (hx : abs x ≤ 1) (hy : abs y ≤ 1) :
    x^2+y^2-2*x^2*y^2+2*x*y*Real.sqrt (1-x^2)*Real.sqrt (1-y^2) =
      (x*Real.sqrt (1-y^2)+y*Real.sqrt (1-x^2))^2 := by
  have hx2 : x^2 ≤ 1 := (sq_le_one_iff_abs_le_one x).mpr hx
  have hy2 : y^2 ≤ 1 := (sq_le_one_iff_abs_le_one y).mpr hy
  have hsx := Real.sq_sqrt (sub_nonneg.mpr hx2)
  have hsy := Real.sq_sqrt (sub_nonneg.mpr hy2)
  linear_combination -y^2 * hsx - x^2 * hsy
