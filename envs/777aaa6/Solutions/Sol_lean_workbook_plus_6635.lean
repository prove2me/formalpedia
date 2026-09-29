-- Prove2me | solution 1 for lean_workbook_plus_6635
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:12.617757+00:00
-- url     : https://prove2.me/submissions/4aacb883-8d8e-4d59-be89-4166ef70e4c0

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 → a + b + c + 2 = a * b * c) := by
  intro h
  have ha' : 1+a ≠ 0 := by positivity
  have hb' : 1+b ≠ 0 := by positivity
  have hc' : 1+c ≠ 0 := by positivity
  field_simp at h
  nlinarith
