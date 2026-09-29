-- Prove2me | solution 1 for lean_workbook_plus_58045
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:57.332985+00:00
-- url     : https://prove2.me/submissions/9fb7572c-e2a4-4396-b24d-624db43e4c05

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a r : ℝ) : a / r + a + a * r = 5 → a * (1 / r + r + 1) = 5 := by
  intros
  grind
