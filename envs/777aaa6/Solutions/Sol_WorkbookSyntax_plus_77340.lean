-- Prove2me | solution 1 for WorkbookSyntax.plus_77340
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:52.084272+00:00
-- url     : https://prove2.me/submissions/18bd9b76-5458-4ec3-b955-b3913b632be6

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : ∑ i ∈ Finset.Icc 1 100, (5^i - 5^(i-1)) = 5^100 - 1   := by
  decide +kernel
#print axioms solution
