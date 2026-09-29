-- Prove2me | solution 1 for WorkbookSyntax.plus_49771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:54.903971+00:00
-- url     : https://prove2.me/submissions/91ae630c-3460-4039-a48e-6505182e63fc

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : ∑ m ∈ Finset.range 16, ∑ n ∈ Finset.range (16 - m), (Nat.choose (m + n) m * Nat.choose 15 (m + n) * 5 ^ n) = ∑ m ∈ Finset.range 16, (Nat.choose 15 m * 6 ^ (15 - m))   := by
  decide +kernel
#print axioms solution
