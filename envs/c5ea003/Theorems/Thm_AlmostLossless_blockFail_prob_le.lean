-- Prove2me | Theorems.Thm_AlmostLossless_blockFail_prob_le
-- name    : AlmostLossless.blockFail_prob_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:02:57.446646+00:00
-- url     : https://prove2.me/theorems/1e9603ac-1685-4477-987a-6b063b07c1e9
-- title:
--   Blocked random-coding bound.
-- statement:
--   **Blocked random-coding bound.**  With one shared random codebook and
--   independent per-block hashing, the failure probability obeys the union bound
--   `P[failure] ≤ b (|T| - 1) / M` — only a factor `b` worse than the flat scheme,
--   while the decoder cost drops from `|T| ^ b` to `b |T|`.
--
--   ```lean
--   theorem AlmostLossless.blockFail_prob_le(T : Finset β) {x : Fin b → β} (hx : ∀ i, x i ∈ T) :
--       M * (blockFail T x M).card ≤ (b * (T.card - 1)) * M ^ (b * Fintype.card β) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessBlock.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessBlock.lean#L134

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

theorem AlmostLossless.blockFail_prob_le(T : Finset β) {x : Fin b → β} (hx : ∀ i, x i ∈ T) :
    M * (blockFail T x M).card ≤ (b * (T.card - 1)) * M ^ (b * Fintype.card β) := by sorry
