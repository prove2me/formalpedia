-- Prove2me | solution 1 for WorkbookSyntax.plus_81229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:53.593368+00:00
-- url     : https://prove2.me/submissions/b2cda674-6a84-4671-a709-f7327d92f877

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (n : ℕ) (h₁ : 150 ≤ n) (h₂ : n ≤ 431) (h₃ : n ∣ 2050) : ∑ k ∈ Finset.filter (λ x => x ∣ 2050) (Finset.Icc 150 431), k = 615   := by
  decide +kernel
#print axioms solution
