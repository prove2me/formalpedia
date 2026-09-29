-- Prove2me | solution 1 for lean_workbook_plus_76396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:21.998834+00:00
-- url     : https://prove2.me/submissions/e20735dd-c3c5-4028-968d-dfcc47e49b3c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 2*x - 5 < 7 ↔ x < 6 := by
  intros
  grind
