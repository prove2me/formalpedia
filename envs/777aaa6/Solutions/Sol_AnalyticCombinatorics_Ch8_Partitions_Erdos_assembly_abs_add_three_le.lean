-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.assembly_abs_add_three_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:19:14.433987+00:00
-- url     : https://prove2.me/submissions/b1407898-95a3-4631-81ae-1b21588a78f9

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

end

open Filter Finset
open scoped Topology BigOperators
theorem solution (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (a + b) c
  have h2 := abs_add_le a b
  nlinarith
