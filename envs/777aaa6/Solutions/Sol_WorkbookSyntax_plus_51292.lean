-- Prove2me | solution 1 for WorkbookSyntax.plus_51292
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:56.506464+00:00
-- url     : https://prove2.me/submissions/4add2bcf-c973-4d77-8789-0866522c37ae

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : (∏ k ∈ Finset.Icc 1 1006, (2 * k - 1)) % 8 = 3   := by
  decide +kernel
#print axioms solution
