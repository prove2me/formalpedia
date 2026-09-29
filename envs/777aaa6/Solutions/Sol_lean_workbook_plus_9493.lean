-- Prove2me | solution 1 for lean_workbook_plus_9493
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:32.58141+00:00
-- url     : https://prove2.me/submissions/fbbe7557-772f-4b1a-ad61-051927707187

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ): (∀ x, f (2 * x) = f x + x) ∧ (∀ x, f (x - f (2 * x)) + x = 0) → ∀ x, f (-f x) = -x := by
  intros
  grind
