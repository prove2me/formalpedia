-- Prove2me | Theorems.Thm_AlmostLossless_card_codebooks
-- name    : AlmostLossless.card_codebooks
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:02:44.744163+00:00
-- url     : https://prove2.me/theorems/5b9f6aa4-9074-4d37-a7cd-c162fe535060
-- title:
--   Total number of codebooks.
-- statement:
--   Total number of codebooks.
--
--   ```lean
--   theorem AlmostLossless.card_codebooks(ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℕ) :
--       Fintype.card (ι → Fin M) = M ^ Fintype.card ι := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessCore.lean#L62

-- Thm stub generated from Geometry/AlmostLosslessCore.lean
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

theorem AlmostLossless.card_codebooks(ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℕ) :
    Fintype.card (ι → Fin M) = M ^ Fintype.card ι := by sorry
