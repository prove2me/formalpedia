-- Prove2me | solution 1 for lean_workbook_plus_34526
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:38.985062+00:00
-- url     : https://prove2.me/submissions/9349ddab-c0ff-4efb-bafa-67e48eb7993e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 3*x - 130 = 0 ↔ x = 13 ∨ x = -10 := by
  intros
  grind
