-- Prove2me | solution 1 for lean_workbook_plus_19090
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:57.969271+00:00
-- url     : https://prove2.me/submissions/0ff8546c-c402-4e7a-848f-761fba8a6c7c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = (6 * x ^ 2 + x + 2) ^ 3 / 27) : f 1 = 27 := by
  intros
  grind
