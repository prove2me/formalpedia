-- Prove2me | Theorems.Thm_CollisionPattern_card_doubleCollision_mul_eq
-- name    : CollisionPattern.card_doubleCollision_mul_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:10:18.697629+00:00
-- url     : https://prove2.me/theorems/60a56d3e-280c-42f5-b22a-e790ec5a24f8
-- title:
--   The second marginal of `AlmostLosslessConverse` is an equality.
-- statement:
--   **The second marginal of `AlmostLosslessConverse` is an equality.**  Two
--   collisions through a common vertex have probability exactly `1/M²`; the
--   inequality `AlmostLossless.card_doubleCollision_mul_le` loses nothing.  (Here
--   `2 ≤ |ι|` is automatic from the three distinct indices, and is used only to
--   handle the exponent arithmetic.)
--
--   ```lean
--   theorem CollisionPattern.card_doubleCollision_mul_eq{p q r : ι} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
--       M ^ 2 * ((collisionEvent M p r) ∩ (collisionEvent M q r)).card
--         = M ^ Fintype.card ι := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/CollisionPatternMarginal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/CollisionPatternMarginal.lean#L172

-- Thm stub generated from Geometry/CollisionPatternMarginal.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_CollisionPatternMarginal
/-
# Which marginals?  Exact marginals of an arbitrary collision pattern

Research thread *Compression Beyond the Pigeonhole Bound*, cycle v19c.

The Bonferroni / second-moment machinery of `Geometry.AlmostLosslessConverse` and
`Geometry.BonferroniMarginals` is indifferent to *which* events it is fed; the
content of a failure bound is entirely in the marginals.  `AlmostLosslessCore`
supplies one exact marginal (`card_collisionEvent_mul`, a single pair) and
`AlmostLosslessConverse` one inequality (`card_doubleCollision_mul_le`, two
pairs through a common vertex).  This file computes **all** of them at once.

The organising principle is geometric: a *collision pattern* `P` is a graph on
the index set `ι`, a codebook satisfying the pattern is a function constant on
each connected component, and the marginal is therefore `M^{#components}`.
Rather than developing quotient combinatorics we encode the component structure
by an idempotent **collapse map** `f : ι → ι` (a choice of representative per
component), whose image is the component set.

Main results.

* `CollisionPattern.card_collapseEvent` — for any idempotent `f : ι → ι`, the set
  of codebooks constant on the fibres of `f` has cardinality exactly
  `M ^ |image f|`.  (Bijection with functions on the image.)
* `CollisionPattern.card_patternEvent_of_collapse` — the exact marginal of a
  collision pattern presented by a collapse map.
* `CollisionPattern.card_starEvent` — the **star marginal**: the event that a
  whole set `T` of competitors collides with a fixed `x ∉ T` has cardinality
  `M ^ (|ι| - |T|)`, i.e. probability `M^{-|T|}`.  All higher Bonferroni terms of
  the almost-lossless analysis are instances.
* `CollisionPattern.card_collisionEvent_eq` — recovers
  `AlmostLossless.card_collisionEvent_mul` (`|T| = 1`).
* `CollisionPattern.card_doubleCollision_mul_eq` — **upgrades**
  `AlmostLossless.card_doubleCollision_mul_le` from `≤` to an *equality*: two
  collisions through a common vertex have probability exactly `1/M²`.
* `CollisionPattern.card_disjointPairs_mul_eq` — two collisions on four distinct
  vertices are *exactly independent*, again `1/M²`.  So the two very different
  geometries of a pair of edges (sharing a vertex or not) have the *same*
  second marginal: the Bonferroni input is blind to the shape of the pattern and
  sees only its component count.
-/

open CollisionPattern

open Finset AlmostLossless

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}

/-! ## 1. Collapse maps and their exact marginals -/





/-! ## 2. The star marginal: `|T|` competitors colliding with a fixed point -/



/-! ## 3. Consequences: the catalog marginals, exactly -/

theorem CollisionPattern.card_doubleCollision_mul_eq{p q r : ι} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    M ^ 2 * ((collisionEvent M p r) ∩ (collisionEvent M q r)).card
      = M ^ Fintype.card ι := by sorry
