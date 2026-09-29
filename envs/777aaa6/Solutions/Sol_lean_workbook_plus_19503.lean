-- Prove2me | solution 1 for lean_workbook_plus_19503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:03.756077+00:00
-- url     : https://prove2.me/submissions/d11f8e5b-3181-4180-854f-5002d97e9049

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℂ) (h : a + b + c + d = 0) : a^3 + b^3 + c^3 + d^3 = 3 * (a * b * c + a * b * d + b * c * d + a * c * d) := by
  intros
  grind
