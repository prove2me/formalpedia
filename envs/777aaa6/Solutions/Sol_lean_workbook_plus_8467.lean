-- Prove2me | solution 1 for lean_workbook_plus_8467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:18.497008+00:00
-- url     : https://prove2.me/submissions/223d150b-65ff-4b69-991f-f098ff430390

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : (1 / 3) * (x ^ 2 + x * y + y ^ 2) + 2 ≥ x + y + 1 := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x+y-2)]
