-- Prove2me | solution 1 for lean_workbook_plus_22842
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:20.84405+00:00
-- url     : https://prove2.me/submissions/81d4728e-b487-4ee3-b9cc-032eb49e7472

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x ≥ 2, (x+1)^8 > x^8 + x^7 - x^5 - x^4 - x^3 + x + 1 := by
  intros
  grind
