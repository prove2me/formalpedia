-- Prove2me | Theorems.Thm_AlmostLossless_card_blockGood_ge
-- name    : AlmostLossless.card_blockGood_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:25.837+00:00
-- url     : https://prove2.me/theorems/f52156e9-9192-4c08-9c85-96cad3c0bc03
-- title:
--   Card blockGood ge
-- statement:
--   Formal statement of `AlmostLossless.card_blockGood_ge` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AlmostLossless.card_blockGood_ge{T : Finset β} {LT : List β} {x : Fin b → β}
--       (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T) :
--       M ^ (b * Fintype.card β) ≤ (blockGood LT x M).card + (blockFail T x M).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessBlock.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessBlock.lean#L179

-- Thm stub generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Beating the decoder-search barrier: the blocked (product) random code

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The single-hash almost-lossless scheme of `Geometry.AlmostLosslessDecoder` has
optimal rate but its decoder scans the whole typical set: cost `|S|`, which is
*exponential* in the block length.  Here we remove that obstacle.

Split a string into `b` blocks over a block alphabet `β`, each block typical in
`T : Finset β`, so the global typical set is the product `T^b`, of size
`|T|^b`.  Draw one random codebook `H : Fin b × β → Fin M` and hash each block
*separately*.  Then:

* `AlmostLossless.blockDecode_cost` — the decoder costs exactly `b * |T|` hash
  comparisons, **linear** in the number of blocks, versus `|T| ^ b` for the flat
  scheme (`AlmostLossless.block_beats_flat`: `b * |T| < |T| ^ b`).
* `AlmostLossless.blockDecode_never_wrong` — no silent corruption survives the
  product construction: a decoded string is always the transmitted one.
* `AlmostLossless.blockFail_prob_le` / `AlmostLossless.blockDecode_success_prob_ge` —
  the price is only a union-bound factor `b` in the failure probability:
  `P[failure] ≤ b (|T| - 1) / M`.
-/

open AlmostLossless

open Finset

variable {β : Type*} [Fintype β] [DecidableEq β] {b M : ℕ}

/-! ## 1. The blocked scheme -/




/-! ## 2. No silent corruption, blockwise -/



/-! ## 3. Success of the blocked decoder -/



/-! ## 4. Failure probability: a union bound over the blocks -/

theorem AlmostLossless.card_blockGood_ge{T : Finset β} {LT : List β} {x : Fin b → β}
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T) :
    M ^ (b * Fintype.card β) ≤ (blockGood LT x M).card + (blockFail T x M).card := by sorry
