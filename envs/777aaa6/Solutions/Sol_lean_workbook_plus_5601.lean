-- Prove2me | solution 1 for lean_workbook_plus_5601
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:47.573656+00:00
-- url     : https://prove2.me/submissions/a1ba1b54-5ffb-468e-a4cd-a74c8e58041b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℝ) : t^2 - 7*t + 10 = 0 ↔ t = 2 ∨ t = 5 := by
  intros
  grind
