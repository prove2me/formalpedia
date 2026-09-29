-- Prove2me | solution 1 for lean_workbook_plus_46602
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:16.429712+00:00
-- url     : https://prove2.me/submissions/58144f0e-3717-4df6-8b42-49c3d47c6bb1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) : 3 * (a + b + c + d) ≤ 8 + a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  have one : ∀t:ℝ,0≤t → 3*t≤2+t^3 := by
    intro t ht
    have hp := mul_nonneg (sq_nonneg (t-1)) (show 0≤t+2 by linarith)
    nlinarith only [hp]
  linarith [one a ha.1,one b hb.1,one c hc.1,one d hd.1]
