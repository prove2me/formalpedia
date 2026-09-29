-- Prove2me | solution 1 for lean_workbook_plus_58188
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:35:36.962215+00:00
-- url     : https://prove2.me/submissions/c4839181-8012-4192-9e34-d4bd2f4fc710

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : |(x + y) / ((1 + x ^ 2) * (1 + y ^ 2))| ≤ 1 := by
  have hd : 0 < (1+x^2)*(1+y^2) := by positivity
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg (x*y), sq_nonneg (x+1/2), sq_nonneg (y+1/2)]
  · apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg (x*y), sq_nonneg (x-1/2), sq_nonneg (y-1/2)]
