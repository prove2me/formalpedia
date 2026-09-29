-- Prove2me | solution 1 for lean_workbook_plus_8030
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:36.833205+00:00
-- url     : https://prove2.me/submissions/f62d8760-903f-4084-b24a-b5bf548fbe72

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, x^2*y + y^2*z + z^2*x = x*y^2 + y*z^2 + z*x^2 ↔ x = y ∨ y = z ∨ z = x := by
  intro x y z
  intros
  grind
