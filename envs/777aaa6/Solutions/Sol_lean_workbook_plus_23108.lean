-- Prove2me | solution 1 for lean_workbook_plus_23108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:46:27.908213+00:00
-- url     : https://prove2.me/submissions/b07182c8-cf6e-4c9f-9fd2-311b00478f42

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)  (h : (a^2 + 2) * (a + b^3 + 1) ≤ 9) : a + b ≤ 2 := by
  have hb3 : 0 ≤ b^3 := pow_nonneg hb 3
  have ha2 : a ≤ 2 := by
    nlinarith [mul_nonneg (sq_nonneg a) hb3,mul_nonneg ha (sq_nonneg a),sq_nonneg (a-2)]
  by_contra hn
  have hgap : 2-a < b := by linarith
  have hcub : (2-a)^3 < b^3 := pow_lt_pow_left₀ hgap (by linarith) (by norm_num)
  have hsq : (a-2)^2 ≤ 4 := by nlinarith [mul_nonneg ha (sub_nonneg.mpr ha2)]
  have hbound : a*(a-2)^2 ≤ (2:ℝ)*4 := mul_le_mul ha2 hsq (sq_nonneg (a-2)) (by norm_num)
  have hf : 0 ≤ 9-a*(a-2)^2 := by linarith only [hbound]
  have hbase := mul_nonneg (sq_nonneg (a-1)) hf
  have hdelta : 0 < (a^2+2)*(b^3-(2-a)^3) := mul_pos (by positivity) (sub_pos.mpr hcub)
  nlinarith only [h,hbase,hdelta]
