-- Prove2me | solution 1 for lean_workbook_plus_48646
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:32.489331+00:00
-- url     : https://prove2.me/submissions/23af8d30-2f64-48c5-bb15-06c814a30afb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (v d t : ℝ)
  (h₀ : 0 < v ∧ 0 < d ∧ 0 < t)
  (h₁ : v * t = d)
  (h₂ : 3 / 2 * v + 4 / 5 * v * (t + 1) = d) :
  d / v = 23 / 2 := by
  apply (div_eq_iff (ne_of_gt h₀.1)).2
  have hv : v*t = 23/2*v := by nlinarith
  linarith
