-- Prove2me | solution 1 for lean_workbook_plus_23652
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:32.869523+00:00
-- url     : https://prove2.me/submissions/2f8fecc9-d6f7-437a-a556-1f41a99a8313

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf: ∀ x, f x + f (-x) = 0) : ∀ x, f x = -f (-x) := by
  intros
  grind
