-- Prove2me | solution 1 for lean_workbook_plus_38433
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:36.157638+00:00
-- url     : https://prove2.me/submissions/d059f589-9aff-4442-a740-18a0df178caa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : Real.sqrt (2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≥ (a + b) * (b + c) * (c + a) - 4 * a * b * c := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg ((a-b)*(a-c)*(b-c))]
