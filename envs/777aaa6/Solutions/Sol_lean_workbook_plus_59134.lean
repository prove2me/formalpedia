-- Prove2me | solution 1 for lean_workbook_plus_59134
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:44.783408+00:00
-- url     : https://prove2.me/submissions/b10f8b3f-3c68-43f2-8109-e4586f3fe833

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (hab : |a| ≥ |b + c|) (hbc : |b| ≥ |c + a|) (hca : |c| ≥ |a + b|) : a + b + c = 0 := by
  intros
  grind
