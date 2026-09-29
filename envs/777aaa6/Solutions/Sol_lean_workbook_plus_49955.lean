-- Prove2me | solution 1 for lean_workbook_plus_49955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:38.202881+00:00
-- url     : https://prove2.me/submissions/949e09ee-aa9d-4a06-bceb-989e33c39bdd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ x : ℝ, x^4 + 2*x^3 + 3*x^2 + 2*x + 1 ≥ 4*x^3 + 4*x^2 := by
  intro x
  intros
  
  have h_identity : (x^4 + 2*x^3 + 3*x^2 + 2*x + 1) - (4*x^3 + 4*x^2) = (1 : ℝ) * 1 * ((1 + x + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^4 + 2*x^3 + 3*x^2 + 2*x + 1) - (4*x^3 + 4*x^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
