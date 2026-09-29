-- Prove2me | solution 1 for lean_workbook_plus_41094
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:39.861573+00:00
-- url     : https://prove2.me/submissions/b6bea816-d504-4d5a-9185-6da04f972c00

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : (Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ (x + y) / 2 ∧ Real.sqrt ((y ^ 2 + z ^ 2) / 2) ≥ (y + z) / 2 ∧ Real.sqrt ((z ^ 2 + x ^ 2) / 2) ≥ (z + x) / 2) := by
  have hpair : ∀ a b : ℝ, (a+b)/2 ≤ Real.sqrt ((a^2+b^2)/2) := by
    intro a b
    apply Real.le_sqrt_of_sq_le
    nlinarith only [sq_nonneg (a-b)]
  exact ⟨hpair x y,hpair y z,hpair z x⟩
