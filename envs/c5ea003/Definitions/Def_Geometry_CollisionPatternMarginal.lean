-- Prove2me | Definitions.Def_Geometry_CollisionPatternMarginal
-- name    : Geometry_CollisionPatternMarginal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:28:56.847928+00:00
-- url     : https://prove2.me/theorems/a88afebc-413f-48fc-b88c-41ff1d68e28a
-- title:
--   Aether Catalog definitions — Geometry_CollisionPatternMarginal
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CollisionPatternMarginal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CollisionPatternMarginal.lean by skeleton subtraction
import Mathlib
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

namespace CollisionPattern

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}

/-! ## 1. Collapse maps and their exact marginals -/

/-- The event that a codebook is constant on the fibres of `f`, i.e. factors
through `f`. -/
def collapseEvent (M : ℕ) (f : ι → ι) : Finset (ι → Fin M) :=
  univ.filter (fun H => ∀ a, H (f a) = H a)


/-- A *collision pattern* `P` (a finite set of pairs, i.e. a graph on `ι`): the
event that a codebook collides on every pair of `P`. -/
def patternEvent (M : ℕ) (P : Finset (ι × ι)) : Finset (ι → Fin M) :=
  univ.filter (fun H => ∀ p ∈ P, H p.1 = H p.2)


/-! ## 2. The star marginal: `|T|` competitors colliding with a fixed point -/

/-- The event that every member of `T` collides with `x`. -/
def starEvent (M : ℕ) (T : Finset ι) (x : ι) : Finset (ι → Fin M) :=
  univ.filter (fun H => ∀ y ∈ T, H y = H x)


/-! ## 3. Consequences: the catalog marginals, exactly -/





end CollisionPattern


