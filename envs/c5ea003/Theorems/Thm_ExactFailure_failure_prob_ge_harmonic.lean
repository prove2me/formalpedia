-- Prove2me | Theorems.Thm_ExactFailure_failure_prob_ge_harmonic
-- name    : ExactFailure.failure_prob_ge_harmonic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:10:40.269832+00:00
-- url     : https://prove2.me/theorems/cb198933-8ca9-4434-96df-448076c35e80
-- title:
--   A matching lower bound, from the exact law.
-- statement:
--   **A matching lower bound, from the exact law.**  Since
--   `(1 + k/M)(1 - 1/M)^k ≤ ((1+1/M)(1-1/M))^k ≤ 1`, the exact law gives
--   `P[failure] ≥ k/(M+k)`.  With `failure_prob_le_shannon` this pins the failure
--   probability of a uniformly random codebook between `k/(M+k)` and `k/M` for every
--   `k` and every `M ≥ 1`: random hashing fails with probability `Θ(min(1, k/M))`.
--
--   ```lean
--   theorem ExactFailure.failure_prob_ge_harmonic(S : Finset α) (x : α) (hM : 0 < M) :
--       ((S.erase x).card : ℝ) / ((M : ℝ) + (S.erase x).card)
--         ≤ ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ExactFailureMarginal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ExactFailureMarginal.lean#L252

-- Thm stub generated from Geometry/ExactFailureMarginal.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_ExactFailureMarginal
/-
# Which marginals?  The exact failure law of the random codebook

Research thread *Compression Beyond the Pigeonhole Bound*, cycle v19c.

`Geometry.AlmostLosslessConverse` obtains `P[failure] ≥ k/(2M)` (for `2(k-1) ≤ M`)
by feeding two marginals into the Bonferroni inequality, and
`Geometry.BonferroniMarginals` improves this to the unconditional `k/(M+k-1)` by
feeding the *same* two marginals into the second-moment inequality.  Both are
lower bounds.  This file closes the question completely: the failure probability
of the uniform random codebook is *computed exactly*,

`P[failure] = 1 - (1 - 1/M)^k`,   `k = |S \ {x}|`,

and both the Shannon upper bound and a matching lower bound are then elementary
consequences.  The mechanism is a **conditional marginal principle**: the
collision event `H y = H x` has probability exactly `1/M` *conditionally on any
event that does not constrain the coordinate `y`*.  That is the precise sense in
which the almost-lossless analysis is a statement about marginals.

Main results.

* `ExactFailure.card_inter_collisionEvent_mul` — the **conditional collision
  marginal**: `M · |G ∩ {H : H y = H x}| = |G|` for every `G` unconstrained at
  `y` (`y ≠ x`).  A strict generalisation of
  `AlmostLossless.card_collisionEvent_mul` (take `G = univ`).
* `ExactFailure.card_noCollisionEvent_mul` — by induction along the competitors:
  `M^k · |{H : H y ≠ H x for all y ∈ D}| = (M-1)^k · M^{|α|}`, `k = |D|`.
* `ExactFailure.card_failSet_exact` — the **exact failure count**
  `M^k · |failSet| + (M-1)^k · M^{|α|} = M^k · M^{|α|}`.
* `ExactFailure.failure_prob_exact` — `P[failure] = 1 - (1 - 1/M)^k`.
* `ExactFailure.failure_prob_le_shannon` — recovers the random-coding bound
  `P[failure] ≤ k/M` (`AlmostLossless.failSet_prob_le`) from the exact law.
* `ExactFailure.failure_prob_ge_harmonic` — the matching lower bound
  `P[failure] ≥ k/(M+k)`, proved from the exact law by Bernoulli's inequality.
  Together the two show `P[failure] = Θ(k/M)` for **all** `k` and `M`.
-/

open ExactFailure

open Finset AlmostLossless

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}

/-! ## 1. The conditional collision marginal -/



/-! ## 2. The no-collision event and its exact count -/





/-! ## 3. The exact failure law of the almost-lossless scheme -/

variable {α : Type*} [Fintype α] [DecidableEq α]




/-! ## 4. Matching upper and lower bounds from the exact law -/

theorem ExactFailure.failure_prob_ge_harmonic(S : Finset α) (x : α) (hM : 0 < M) :
    ((S.erase x).card : ℝ) / ((M : ℝ) + (S.erase x).card)
      ≤ ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
