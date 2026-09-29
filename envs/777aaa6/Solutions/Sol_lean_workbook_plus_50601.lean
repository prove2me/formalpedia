-- Prove2me | solution 1 for lean_workbook_plus_50601
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:40:39.653693+00:00
-- url     : https://prove2.me/submissions/5fc2bf09-952c-48f6-8d5f-071c8335eb56

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℝ) :  |a - b| / (1 + |a - b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
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
  have hab : |a-b| ≤ |a|+|b| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  exact transfer |a| |b| |a-b| (abs_nonneg a) (abs_nonneg b) (abs_nonneg (a-b)) hab
