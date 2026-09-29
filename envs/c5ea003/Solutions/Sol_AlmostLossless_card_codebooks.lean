-- Prove2me | solution 1 for AlmostLossless.card_codebooks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:06:40.976533+00:00
-- url     : https://prove2.me/submissions/907c146f-fa0c-4c46-b1d3-f29093a072c5

-- Sol generated from Geometry/AlmostLosslessCore.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
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

open AlmostLossless

open Finset

/-! ## 1. The pigeonhole barrier for exact decoding -/



/-! ## 2. The finite probability space of codebooks

The sample space is the (finite) set of *all* functions `H : ι → Fin M`;
"probability" means normalised counting measure, and we keep everything in the
integers by multiplying through by the total number `M ^ |ι|` of codebooks. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}







open AlmostLossless in
theorem solution(ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℕ) :
    Fintype.card (ι → Fin M) = M ^ Fintype.card ι := by
  simp
