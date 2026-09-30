-- Prove2me | solution 2 for lean_workbook_plus_6732
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:11.851932+00:00
-- url     : https://prove2.me/submissions/0f5c4673-4747-4e48-8e39-e05b4448d88b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (f_def : ∀ x, x < 5 → f x = 3 * x + 6 ∧ ∀ x, 5 ≤ x → f x = 7 * x - 20) : f (f (f 2)) = 428 := by
  intros
  grind
