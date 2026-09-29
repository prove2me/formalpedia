-- Prove2me | Theorems.Thm_AlmostLossless_blockDecode_success_prob_ge
-- name    : AlmostLossless.blockDecode_success_prob_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:35.409674+00:00
-- url     : https://prove2.me/theorems/52ca7e9e-f698-479c-a14a-f23e31bc7f9e
-- title:
--   Almost-lossless guarantee for the blocked scheme.
-- statement:
--   **Almost-lossless guarantee for the blocked scheme.**  If
--   `M ≥ b (|T| - 1) / ε` then a uniformly random codebook recovers a fixed typical
--   string with probability at least `1 - ε`, using exactly `b |T|` hash
--   comparisons.
--
--   ```lean
--   theorem AlmostLossless.blockDecode_success_prob_ge{T : Finset β} {LT : List β} {x : Fin b → β}
--       (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
--       (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
--       (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
--       1 - ε ≤ ((blockGood LT x M).card : ℝ) / ((M : ℝ) ^ (b * Fintype.card β)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessBlock.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessBlock.lean#L199

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

theorem AlmostLossless.blockDecode_success_prob_ge{T : Finset β} {LT : List β} {x : Fin b → β}
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
    (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
    1 - ε ≤ ((blockGood LT x M).card : ℝ) / ((M : ℝ) ^ (b * Fintype.card β)) := by sorry
