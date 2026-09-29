-- Prove2me | solution 1 for lean_workbook_plus_48271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:50.009867+00:00
-- url     : https://prove2.me/submissions/103c4773-a335-41be-b48b-a6fe15874968

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 28 * x^5 + 3 * x^4 - 29 * x^3 + 4 * x^2 - 7 * x + 1)
  : f 1 = 0 := by
  intros
  grind
