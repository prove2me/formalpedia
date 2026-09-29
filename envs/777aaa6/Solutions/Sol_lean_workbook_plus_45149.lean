-- Prove2me | solution 1 for lean_workbook_plus_45149
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:06.7988+00:00
-- url     : https://prove2.me/submissions/8c456a14-d4a5-4f3c-ae55-e59c066eb2b4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2): a * (a + b) + b * (b + c) + c * (c + a) ≥ a ^ 3 + b ^ 3 + c ^ 3 := by
  have one : ∀t:ℝ,1≤t → t≤2 → 0≤(t+2)*(t-1)*(2-t) := by
    intro t ht hu
    exact mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr ht)) (sub_nonneg.mpr hu)
  have h1 := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  have h2 := mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hc.2)
  have h3 := mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr ha.2)
  nlinarith only [one a ha.1 ha.2,one b hb.1 hb.2,one c hc.1 hc.2,h1,h2,h3]
