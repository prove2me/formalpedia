-- Prove2me | solution 1 for lean_workbook_plus_25467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:05:21.241319+00:00
-- url     : https://prove2.me/submissions/14df6a46-4660-4718-ad9c-5c48469b0ccb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (b + c) / a + (c + a) / b = 9) :
  (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 88 / 7 := by
  clear habc
  have hpoly : 11*a*b=(a+b)*(a+b+c) := by
    have hh := h
    field_simp [ne_of_gt ha,ne_of_gt hb] at hh
    nlinarith only [hh]
  have ht : 0 ≤ (7*(a+b)-4*c)*(a+b) := by
    nlinarith only [hpoly,sq_nonneg (a-b)]
  have hcs := (mul_nonneg_iff_of_pos_right (add_pos ha hb)).mp ht
  have hratio : (4:ℝ)/7 ≤ (a+b)/c := by
    apply (le_div_iff₀ hc).2
    linarith only [hcs]
  have he : (a+b+c)*(1/a+1/b+1/c)=3+((b+c)/a+(c+a)/b)+(a+b)/c := by
    field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hc] <;> ring
  rw [he,h]
  linarith only [hratio]
