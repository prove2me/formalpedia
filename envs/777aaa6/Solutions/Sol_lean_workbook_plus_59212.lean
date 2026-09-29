-- Prove2me | solution 1 for lean_workbook_plus_59212
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:26.855807+00:00
-- url     : https://prove2.me/submissions/e64be08f-775c-4301-a01d-37e13dc869a6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (α : ℝ) (h : α > 1.41313) : α ^ 12 > 61 := by
  have hmono : (1.41313 : ℝ)^12 ≤ α^12 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt h) 12
  have hnum : (61 : ℝ) < (1.41313 : ℝ)^12 := by norm_num
  exact lt_of_lt_of_le hnum hmono
