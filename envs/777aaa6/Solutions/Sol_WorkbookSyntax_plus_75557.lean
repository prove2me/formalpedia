-- Prove2me | solution 1 for WorkbookSyntax.plus_75557
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:51.561443+00:00
-- url     : https://prove2.me/submissions/a0444949-56a6-480b-bcf1-0fdd89d76dc6

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution :
  ∑ k ∈ (Nat.properDivisors 6), k = 6   := by
  decide +kernel
#print axioms solution
