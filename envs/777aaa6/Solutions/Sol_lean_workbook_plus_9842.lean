-- Prove2me | solution 1 for lean_workbook_plus_9842
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:54.748693+00:00
-- url     : https://prove2.me/submissions/e1aee188-15e3-4046-8e19-2e6d9bf89ca6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) : a + b + c - a * b - b * c - c * a ≤ 1 := by
  have hp := mul_nonneg (mul_nonneg ha.1 hb.1) hc.1
  have hq := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)) (sub_nonneg.mpr hc.2)
  nlinarith only [hp,hq]
