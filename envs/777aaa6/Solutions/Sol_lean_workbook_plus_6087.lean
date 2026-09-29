-- Prove2me | solution 1 for lean_workbook_plus_6087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:20.885817+00:00
-- url     : https://prove2.me/submissions/f6f70959-e58d-43f5-8896-400bf6a95290

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z c : ℂ) : 7 - 4 * z = 13 * c ↔ z = (7 - 13 * c) / 4 := by
  intros
  grind
