-- Prove2me | solution 1 for lean_workbook_plus_1964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:40.590937+00:00
-- url     : https://prove2.me/submissions/25bc8a51-3b24-45d4-a194-d546adcbfb18

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z a b c t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≥ x) (hbc : b ≥ y) (hca : c ≥ z) (h : t ≥ 0) : (a + t) / (x + t) + (b + t) / (y + t) + (c + t) / (z + t) ≤ a / x + b / y + c / z := by
  have one : ∀u v:ℝ,0<v → v≤u → (u+t)/(v+t)≤u/v := by
    intro u v hv huv
    apply (div_le_div_iff₀ (by linarith) hv).2
    have hp := mul_nonneg (sub_nonneg.mpr huv) h
    nlinarith only [hp]
  linarith [one a x hx hab,one b y hy hbc,one c z hz hca]
