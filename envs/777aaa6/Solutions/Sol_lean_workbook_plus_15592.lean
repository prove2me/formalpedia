-- Prove2me | solution 1 for lean_workbook_plus_15592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:19.55267+00:00
-- url     : https://prove2.me/submissions/2897545c-844a-4e8c-b6a0-f8d31dddc557

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) :  |a+b| / (1 + |a+b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
  have hlemma (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : z ≤ x+y) :
      z/(1+z) ≤ x/(1+x)+y/(1+y) := by
    have hp : 0 < 1+x := by positivity
    have hq : 0 < 1+y := by positivity
    have hr : 0 < 1+x+y := by positivity
    have hs : 0 < 1+z := by positivity
    calc
      z/(1+z) ≤ (x+y)/(1+x+y) := (div_le_div_iff₀ hs hr).mpr (by nlinarith)
      _ ≤ x/(1+x)+y/(1+y) := by
        apply (div_le_iff₀ hr).mpr
        field_simp
        nlinarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) hx, mul_nonneg (mul_nonneg hx hy) hy]
  exact hlemma |a| |b| |a+b| (abs_nonneg a) (abs_nonneg b) (abs_nonneg (a+b)) (abs_add_le a b)
