-- Prove2me | solution 1 for WorkbookSyntax.plus_51761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:57.2692+00:00
-- url     : https://prove2.me/submissions/a284d441-233c-46c6-8aff-af4cfbe20957

import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution :
  (∑ k ∈ (Nat.divisors 576), 1) = 21   := by
  decide +kernel
#print axioms solution
