-- Prove2me | solution 1 for lean_workbook_plus_19951
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:19.967537+00:00
-- url     : https://prove2.me/submissions/3b70be6d-0fca-4976-8302-a1ee5e6438ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :
  (3 * (a^2 + b^2 + c^2) / 3)^3 ≥ (27 / 8) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) := by
  intros
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - c^2), sq_nonneg (a^3 - c^3), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3)]
