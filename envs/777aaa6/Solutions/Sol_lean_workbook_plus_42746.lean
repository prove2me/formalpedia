-- Prove2me | solution 1 for lean_workbook_plus_42746
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:46.071586+00:00
-- url     : https://prove2.me/submissions/66b30f7b-5d1f-4289-bc6f-0a993024f374

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : a * (1 - a) * (3 - 2 * b) + b * (1 - b) * (3 - 2 * a) ≥ 0 := by
  have h1 := mul_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr ha.2)) (show 0 ≤ 3-2*b by linarith [hb.2])
  have h2 := mul_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)) (show 0 ≤ 3-2*a by linarith [ha.2])
  exact add_nonneg h1 h2
