-- Prove2me | solution 1 for lean_workbook_plus_73133
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:46.936595+00:00
-- url     : https://prove2.me/submissions/35d644f1-5459-4b46-adc2-d7bf34261ad3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℤ, x^2 + y^2 + 6 * x * y = z^2 ↔ x * (x + 6 * y) = (z - y) * (z + y) := by
  intro x y z
  intros
  grind
