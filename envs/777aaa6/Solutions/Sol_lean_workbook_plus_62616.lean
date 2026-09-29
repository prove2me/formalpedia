-- Prove2me | solution 1 for lean_workbook_plus_62616
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:31:33.726295+00:00
-- url     : https://prove2.me/submissions/6e92bf71-5d26-4d18-94bb-53d49f4aeb46

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a : ℝ) (ha : a > 0) (h : a^4 = a + 1) : a^7 < a + 3 := by
  have hgt : 1 < a := by
    by_contra hn
    have hle : a ≤ 1 := le_of_not_gt hn
    have hp := pow_le_pow_left₀ (le_of_lt ha) hle 4
    norm_num at hp
    nlinarith only [hp,h,ha]
  have hmul : a*a^3 < a*2 := by nlinarith only [h,hgt]
  have hcube : a^3 < 2 := (mul_lt_mul_iff_right₀ ha).mp hmul
  have hseven : a^7 = a^4+a^3 := by
    calc
      a^7 = a^3*a^4 := by ring
      _ = a^3*(a+1) := by rw [h]
      _ = a^4+a^3 := by ring
  linarith only [hseven,h,hcube]
