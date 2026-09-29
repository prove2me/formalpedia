-- Prove2me | solution 1 for lean_workbook_plus_52659
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:49.120321+00:00
-- url     : https://prove2.me/submissions/1a245023-8c36-4c85-bf42-d6027542c87c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :
  a * b + b * c + c * a = 1 ↔ a * (b + c) = 1 - b * c := by
  intros
  grind
