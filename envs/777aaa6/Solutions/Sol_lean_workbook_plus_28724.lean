-- Prove2me | solution 1 for lean_workbook_plus_28724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:39.464806+00:00
-- url     : https://prove2.me/submissions/04720c1a-b3c1-4474-ac95-52092c57975a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a : ℝ, a + a^3 - a^4 - a^6 < 1 := by
  intro a
  nlinarith only [sq_nonneg (a^3-1/2),sq_nonneg (a^2-1/2),sq_nonneg (a-1/2)]
