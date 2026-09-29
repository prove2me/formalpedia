-- Prove2me | solution 1 for lean_workbook_plus_40606
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:23.921692+00:00
-- url     : https://prove2.me/submissions/e399c878-9a78-49e6-b983-53a474e34633

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 16 / (1 + a * b * c * d) ≤ 8 / Real.sqrt (a * b * c * d) := by
  have hp : 0<a*b*c*d := by positivity
  have hs := Real.sq_sqrt hp.le
  have hr := Real.sqrt_pos.mpr hp
  apply (div_le_div_iff₀ (by positivity : 0<1+a*b*c*d) hr).mpr
  nlinarith only [hs,sq_nonneg (Real.sqrt (a*b*c*d)-1)]
