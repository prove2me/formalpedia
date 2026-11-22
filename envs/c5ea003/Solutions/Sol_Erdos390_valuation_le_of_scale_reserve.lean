-- Prove2me | solution 1 for Erdos390.valuation_le_of_scale_reserve
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-06T05:51:37.913765+00:00
-- url     : https://prove2.me/submissions/1462cd84-9d58-448b-9145-c70a002f5015

import Mathlib

theorem solution
    {vD vP : ℕ} {cAnchor cTail scale : ℝ}
    (hscale : 0 ≤ scale)
    (hD : (vD : ℝ) ≤ cAnchor * scale)
    (hP : cTail * scale ≤ (vP : ℝ))
    (hcoeff : cAnchor ≤ cTail) :
    vD ≤ vP := by
  have hreal : (vD : ℝ) ≤ (vP : ℝ) :=
    hD.trans ((mul_le_mul_of_nonneg_right hcoeff hscale).trans hP)
  exact_mod_cast hreal
