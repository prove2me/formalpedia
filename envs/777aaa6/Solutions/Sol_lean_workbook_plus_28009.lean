-- Prove2me | solution 1 for lean_workbook_plus_28009
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:11.824174+00:00
-- url     : https://prove2.me/submissions/72f0d068-8579-42c9-98a0-aa5a53b3045d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b ∧ b ≤ 1) (hc : 0 < c ∧ c ≤ 1) : a + b + c + 3 * a * b * c ≥ 2 * (a * b + b * c + c * a) := by
  have h1 := mul_nonneg (mul_nonneg ha.1.le (sub_nonneg.mpr hb.2)) (sub_nonneg.mpr hc.2)
  have h2 := mul_nonneg (mul_nonneg hb.1.le (sub_nonneg.mpr hc.2)) (sub_nonneg.mpr ha.2)
  have h3 := mul_nonneg (mul_nonneg hc.1.le (sub_nonneg.mpr ha.2)) (sub_nonneg.mpr hb.2)
  nlinarith only [h1,h2,h3]
