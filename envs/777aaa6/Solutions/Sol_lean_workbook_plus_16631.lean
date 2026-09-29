-- Prove2me | solution 1 for lean_workbook_plus_16631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:49.363951+00:00
-- url     : https://prove2.me/submissions/3855e96f-66fa-4522-afb7-71e20a09fa46

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a a' s : ℝ) (ha : 0 < a) (ha' : 0 < a') (hs : 0 < s) : √((2 * s) / a) / √((2 * s) / a') = √(a' / a) := by
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  field_simp
