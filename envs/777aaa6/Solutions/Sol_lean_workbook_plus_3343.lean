-- Prove2me | solution 1 for lean_workbook_plus_3343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:39.880648+00:00
-- url     : https://prove2.me/submissions/d970fe76-e4b5-4e9d-83f0-e650a7bc9a7a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf1 : f 1 = 2) (hf2 : ∀ x, f (x + 1) + f x = 1) : ∀ x, f (x + 2) = f x := by
  intros
  grind
