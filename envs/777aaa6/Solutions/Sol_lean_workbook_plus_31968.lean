-- Prove2me | solution 1 for lean_workbook_plus_31968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:11.880369+00:00
-- url     : https://prove2.me/submissions/a8a0aec2-dec5-4b82-92a0-3dc48886071c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, (x ^ 3 + y ^ 3 + z ^ 3 + 2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) - 3 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) ≥ 0 ↔ 2 * (x ^ 3 + y ^ 3 + z ^ 3) + 4 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) - 6 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) ≥ 0) := by
  intro x y z
  intros
  grind
