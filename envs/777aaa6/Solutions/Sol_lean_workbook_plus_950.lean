-- Prove2me | solution 1 for lean_workbook_plus_950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:35.262893+00:00
-- url     : https://prove2.me/submissions/3ae11db1-33ea-43e5-a926-c91d03e45810

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℝ) (h₁ : k > 0) (h₂ : k^3 / 4 = 7 * k / 3) : k = Real.sqrt (28 / 3) := by
  have hm : k*(k^2-28/3)=0 := by nlinarith only [h₂]
  have hk2 : k^2=28/3 := by rcases mul_eq_zero.mp hm with hh|hh; linarith; linarith
  exact ((Real.sqrt_eq_iff_eq_sq (by norm_num) h₁.le).mpr hk2.symm).symm
