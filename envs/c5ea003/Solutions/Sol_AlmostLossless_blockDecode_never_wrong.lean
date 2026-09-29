-- Prove2me | solution 1 for AlmostLossless.blockDecode_never_wrong
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:30:50.603652+00:00
-- url     : https://prove2.me/submissions/8ee16e39-0dd6-4f81-84a6-44332dd1d8cd

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_decode_never_wrong
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

omit [Fintype β] [DecidableEq β] in
/-- If the blocked decoder outputs a string, every block decoded successfully. -/
theorem blockDecode_blocks {LT : List β} {H : Fin b × β → Fin M} {c : Fin b → Fin M}
    {z : Fin b → β} (h : (blockDecode LT H c).1 = some z) :
    ∀ i, (decode LT (fun y => H (i, y)) (c i)).1 = some (z i) := by
  simp only [blockDecode] at h
  by_cases hall : ∀ i : Fin b, ((decode LT (fun y => H (i, y)) (c i)).1).isSome
  · rw [dif_pos hall] at h
    have hz : (fun i => ((decode LT (fun y => H (i, y)) (c i)).1).get (hall i)) = z :=
      Option.some_injective _ h
    intro i
    rw [← hz]
    exact (Option.some_get (hall i)).symm
  · rw [dif_neg hall] at h
    exact absurd h (by simp)


/-! ## 3. Success of the blocked decoder -/



/-! ## 4. Failure probability: a union bound over the blocks -/






/-! ## 5. The complexity separation -/


  


open AlmostLossless in
omit [Fintype β] [DecidableEq β] in
theorem solution{LT : List β} {H : Fin b × β → Fin M}
    {x z : Fin b → β} (hx : ∀ i, x i ∈ LT)
    (h : (blockDecode LT H (blockEncode H x)).1 = some z) : z = x := by
  funext i
  have hi := blockDecode_blocks h i
  exact decode_never_wrong (hx i) hi
