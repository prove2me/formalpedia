-- Prove2me | Theorems.Thm_ExactFailure_card_failSet_exact
-- name    : ExactFailure.card_failSet_exact
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:10:38.492772+00:00
-- url     : https://prove2.me/theorems/e6a2e56b-df5e-4b8d-b0d2-8f90f1ec5179
-- title:
--   The exact failure count.
-- statement:
--   **The exact failure count.**  With `k = |S \ {x}|` competitors,
--   `M^k · |failSet| + (M-1)^k · M^{|α|} = M^k · M^{|α|}`, i.e.
--   `P[failure] = 1 - (1 - 1/M)^k` exactly.  Every bound in the thread —
--   `AlmostLossless.failSet_prob_le`, `AlmostLossless.failure_prob_lower_bound_real`,
--   `BonferroniMarginals.hashing_failure_lower_unconditional` — is a consequence.
--
--   ```lean
--   theorem ExactFailure.card_failSet_exact(S : Finset α) (x : α) :
--       M ^ (S.erase x).card * (failSet S x M).card
--           + (M - 1) ^ (S.erase x).card * M ^ Fintype.card α
--         = M ^ (S.erase x).card * M ^ Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ExactFailureMarginal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ExactFailureMarginal.lean#L181

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

theorem ExactFailure.card_failSet_exact(S : Finset α) (x : α) :
    M ^ (S.erase x).card * (failSet S x M).card
        + (M - 1) ^ (S.erase x).card * M ^ Fintype.card α
      = M ^ (S.erase x).card * M ^ Fintype.card α := by sorry
