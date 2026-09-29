-- Prove2me | solution 1 for lean_workbook_plus_1598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:40:37.43613+00:00
-- url     : https://prove2.me/submissions/e2afb4e5-261d-4406-b90a-dcb7dba96a56

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (x y : ℝ) : |x + y| / (1 + |x + y|) ≤ |x| / (1 + |x|) + |y| / (1 + |y|) := by
  have transfer : ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → w ≤ u+v →
      w/(1+w) ≤ u/(1+u)+v/(1+v) := by
    intro u v w hu hv hw h
    have hm : w/(1+w) ≤ (u+v)/(1+(u+v)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [h]
    have hu' : u/(1+(u+v)) ≤ u/(1+u) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg hu hv]
    have hv' : v/(1+(u+v)) ≤ v/(1+v) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg hu hv]
    calc
      w/(1+w) ≤ (u+v)/(1+(u+v)) := hm
      _ = u/(1+(u+v))+v/(1+(u+v)) := by rw [add_div]
      _ ≤ u/(1+u)+v/(1+v) := add_le_add hu' hv'
  exact transfer |x| |y| |x+y| (abs_nonneg x) (abs_nonneg y) (abs_nonneg (x+y)) (abs_add_le x y)
