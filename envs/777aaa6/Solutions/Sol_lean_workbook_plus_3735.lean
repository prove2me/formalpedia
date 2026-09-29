-- Prove2me | solution 1 for lean_workbook_plus_3735
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:46:30.672114+00:00
-- url     : https://prove2.me/submissions/f2ae8ddb-16fd-4949-a896-85a89a47ea0d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b * (a + 2 * b - 10) + 8 * (3 * a + b) ≥ 25 := by
  have hau : 0 ≤ a-1 := sub_nonneg.mpr ha
  have hbv : 0 ≤ b-1 := sub_nonneg.mpr hb
  have hs : 0 ≤ (b-1)*(a-2)^2 + 2*(a-1)*(b-2)^2 + (a+b-2)^2 + (b-1)^2 + 2*(b-1) := by positivity
  nlinarith only [hs,ha]
