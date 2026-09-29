-- Prove2me | solution 1 for lean_workbook_plus_33290
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:25.983451+00:00
-- url     : https://prove2.me/submissions/30f37e62-01fd-4d27-b394-2a11a319b60e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) :
  |max a b - max c d| ≤ max (|a - c|) (|b - d|) := by
  intros
  grind
