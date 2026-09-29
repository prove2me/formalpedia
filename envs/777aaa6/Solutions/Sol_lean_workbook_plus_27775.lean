-- Prove2me | solution 1 for lean_workbook_plus_27775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:33.961861+00:00
-- url     : https://prove2.me/submissions/d8eacd04-99b6-4b81-8f22-ce114b8f8d27

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) :
  (Real.sqrt (x^2 - 2*x + 10) + Real.sqrt (x^2 - 16*x + 80))^2 ≥
  x^2 - 2*x + 10 + x^2 - 16*x + 80 + 2 * Real.sqrt ((x-1)^2 + 3^2) * Real.sqrt ((x-8)^2 + 4^2) := by
  intros
  grind
