-- Prove2me | solution 1 for lean_workbook_plus_43255
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:32.990204+00:00
-- url     : https://prove2.me/submissions/cde43a54-e540-4421-b584-692acca21696

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : (3*x-4*y+2 = 0 ∧ 2*y+2 = 0) ↔ x = -2 ∧ y = -1 := by
  intros
  grind
