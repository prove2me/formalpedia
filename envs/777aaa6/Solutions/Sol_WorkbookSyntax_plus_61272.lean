-- Prove2me | solution 1 for WorkbookSyntax.plus_61272
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:20:38.573103+00:00
-- url     : https://prove2.me/submissions/c0500095-cd30-41bc-8bd3-14bd6675e307

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : ∑ k ∈ Finset.range 21, k^3 = 44100   := by
  decide +kernel
#print axioms solution
