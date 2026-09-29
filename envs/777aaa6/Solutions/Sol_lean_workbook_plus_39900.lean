-- Prove2me | solution 1 for lean_workbook_plus_39900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:19.388092+00:00
-- url     : https://prove2.me/submissions/5a623783-f3e0-406b-9a94-a9e4969b8c44

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x + 2 > 0 ↔ x > -2 := by
  intros
  grind
