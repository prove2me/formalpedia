-- Prove2me | solution 1 for lean_workbook_plus_9926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:42.492119+00:00
-- url     : https://prove2.me/submissions/da899aef-07f4-4fbe-ad0c-090625161b2d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf : ∀ x ≠ 0, 3 * f (1 / x) + (2 * f x) / x = x^2) : f (-2) = 67 / 20 := by
  intros
  grind
