-- Prove2me | solution 1 for lean_workbook_plus_9856
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:32.814606+00:00
-- url     : https://prove2.me/submissions/2e3548ac-3bc5-47bb-99c6-12eb78ab04ca

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  (1 / 4 * (23 + Real.sqrt 513)) * (1 / 4 * (23 - Real.sqrt 513)) = 1 := by
  intros
  grind
