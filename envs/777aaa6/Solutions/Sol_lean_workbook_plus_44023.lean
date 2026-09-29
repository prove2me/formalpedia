-- Prove2me | solution 1 for lean_workbook_plus_44023
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:08.946786+00:00
-- url     : https://prove2.me/submissions/9b0a8409-065c-4167-afdc-c7a1f20c066b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, (2 / 27 ≥ 2 / 3 * (x * y + x * z + y * z) ^ 2 ↔ 1 ≥ 9 * (x * y + x * z + y * z) ^ 2) := by
  intro x y z
  intros
  grind
