-- Prove2me | solution 1 for lean_workbook_plus_60718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:14.468813+00:00
-- url     : https://prove2.me/submissions/70b4ba6d-1cb5-4f14-b86b-3e5739f8e199

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (h : a + b + c = 0) :
  2 * (a^4 + b^4 + c^4) = (a^2 + b^2 + c^2)^2 := by
  intros
  grind
