-- Prove2me | solution 1 for lean_workbook_plus_6839
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:35.012929+00:00
-- url     : https://prove2.me/submissions/cccbe256-36d5-4960-87df-ab8f4d0d2f27

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + 6*x - 16 = 0 ↔ x = -8 ∨ x = 2 := by
  intros
  grind
