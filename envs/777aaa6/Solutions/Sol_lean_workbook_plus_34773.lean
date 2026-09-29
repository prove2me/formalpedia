-- Prove2me | solution 1 for lean_workbook_plus_34773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:00.900255+00:00
-- url     : https://prove2.me/submissions/eadeba44-fe78-46d9-b42c-72ef5d77172a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a * (a + b) * (a + c) ≥ (a + b) * b * c + (a + c) * b * c ↔ (a^2 - b * c) * (a + b + c) ≥ 0 := by
  intros
  grind
