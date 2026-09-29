-- Prove2me | solution 1 for WorkbookSyntax.plus_58729
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:17.210733+00:00
-- url     : https://prove2.me/submissions/c3a84343-6880-4068-9f12-b2c36f58f737

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (n : ℕ) : ∑ k ∈ Finset.range (49+1), (-1 : ℤ)^k * (99).choose (2 * k) = (-1 : ℤ)^49 * 2^49   := by
  decide +kernel
#print axioms solution
