-- Prove2me | Definitions.Def_Geometry_AlmostLosslessCore
-- name    : Geometry_AlmostLosslessCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:34:40.304166+00:00
-- url     : https://prove2.me/theorems/7178b348-de54-4183-b533-c336958a4a67
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessCore
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessCore.lean by skeleton subtraction
import Mathlib
/-
# Almost-lossless (Monte-Carlo) compression: the random-hash core

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

This file develops, from scratch, the counting core of Shannon's random-coding
argument in a purely finitary, `Finset`-based form:

* `AlmostLossless.pigeonhole_barrier` — the exact/all-strings barrier:
  an injective encoder into `Fin M` forces `M ≥ |α|`.
* `AlmostLossless.collisionEvent` — the event `H p = H q` inside the finite
  probability space of *all* codebooks `H : ι → Fin M`.
* `AlmostLossless.card_collisionEvent_mul` — the exact marginal count
  `M * |{H | H p = H q}| = M ^ |ι|` for `p ≠ q`, i.e. the collision
  probability of a fixed pair is exactly `1/M`.
* `AlmostLossless.card_multiCollision_mul_le` — the union bound in counting
  form for an arbitrary finite family of pairs.

Everything is stated with integer arithmetic (no measure theory), so all
probability statements are exact counting identities/inequalities.
-/

namespace AlmostLossless

open Finset

/-! ## 1. The pigeonhole barrier for exact decoding -/



/-! ## 2. The finite probability space of codebooks

The sample space is the (finite) set of *all* functions `H : ι → Fin M`;
"probability" means normalised counting measure, and we keep everything in the
integers by multiplying through by the total number `M ^ |ι|` of codebooks. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-- The event that a random codebook collides on the (distinct) pair `p, q`. -/
def collisionEvent (M : ℕ) (p q : ι) : Finset (ι → Fin M) :=
  univ.filter (fun H => H p = H q)


/-- The event that a random codebook collides on *some* pair from a finite list of
pairs of distinct points. -/
def multiCollision (M : ℕ) (P : Finset (ι × ι)) : Finset (ι → Fin M) :=
  univ.filter (fun H => ∃ p ∈ P, H p.1 = H p.2)


end AlmostLossless


