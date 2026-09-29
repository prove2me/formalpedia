-- Prove2me | solution 1 for lean_workbook_plus_13196
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:40.998881+00:00
-- url     : https://prove2.me/submissions/c7cc2362-c2bb-4b37-b0af-b6655f44c5dd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (x : ℝ) (f_def : f x = x^2 - 2) : f x = 0 ↔ x = √2 ∨ x = -√2 := by
  intros
  grind
