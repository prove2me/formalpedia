-- Prove2me | solution 1 for lean_workbook_plus_7888
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:07.914557+00:00
-- url     : https://prove2.me/submissions/5199a642-e720-43a6-9ca0-065b420195ac

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (Real.sqrt 14)^2 = 14 ∧ (6 - Real.sqrt 3)^2 = 39 - 12 * Real.sqrt 3 := by
  intros
  grind
