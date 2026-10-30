-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_add_five_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:19:32.816993+00:00
-- url     : https://prove2.me/submissions/bf4e7db9-abee-43a8-8e4c-10c3bf92d02a

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

/-! ### Small lemmas -/

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

set_option maxHeartbeats 4000000
open Filter Finset
open scoped Topology BigOperators
theorem solution (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  nlinarith
