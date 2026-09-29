-- Prove2me | solution 1 for lean_workbook_plus_12679
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:32.669908+00:00
-- url     : https://prove2.me/submissions/5fe924a2-a25c-415c-a57f-9927bd89e494

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (h : ∀ x y z : ℝ, (x + y + z) * f (x * y * z) = 0) : f 0 = 0 := by
  simpa using h 1 0 0
