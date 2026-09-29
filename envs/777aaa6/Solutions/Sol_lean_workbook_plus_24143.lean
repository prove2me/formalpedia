-- Prove2me | solution 1 for lean_workbook_plus_24143
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:40:35.897979+00:00
-- url     : https://prove2.me/submissions/9a574e41-d91a-4efd-935e-5487ca897189

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b c : ℝ) : 
  |a + b - c| + |b + c - a| + |c + a - b| ≥ |a - b| + |b - c| + |c - a| := by
  have h1 := abs_add_le (c+a-b) (-(b+c-a))
  have h2 := abs_add_le (a+b-c) (-(c+a-b))
  have h3 := abs_add_le (b+c-a) (-(a+b-c))
  have e1 : (c+a-b)+(-(b+c-a)) = 2*(a-b) := by ring
  have e2 : (a+b-c)+(-(c+a-b)) = 2*(b-c) := by ring
  have e3 : (b+c-a)+(-(a+b-c)) = 2*(c-a) := by ring
  rw [e1,abs_mul,abs_neg] at h1
  rw [e2,abs_mul,abs_neg] at h2
  rw [e3,abs_mul,abs_neg] at h3
  norm_num at h1 h2 h3
  linarith only [h1,h2,h3]
