-- Prove2me | solution 1 for AlmostLossless.blockDecode_success
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:22:28.197665+00:00
-- url     : https://prove2.me/submissions/5a6c5c9e-9471-4b77-a367-488a0782d64e

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_blockDecode_cost
import Theorems.Thm_AlmostLossless_decode_success_of_not_mem_failSet
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






/-! ## 5. The complexity separation -/


  


open AlmostLossless in
theorem solution{T : Finset β} {LT : List β} {x : Fin b → β}
    {H : Fin b × β → Fin M} (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T)
    (hx : ∀ i, x i ∈ T) (hH : H ∉ blockFail T x M) :
    blockDecode LT H (blockEncode H x) = (some x, b * LT.length) := by
  have hblock : ∀ i : Fin b,
      decode LT (fun y => H (i, y)) (H (i, x i)) = (some (x i), LT.length) := by
    intro i
    refine decode_success_of_not_mem_failSet hnd hmem (hx i) ?_
    intro hmemf
    simp only [failSet, mem_filter, mem_univ, true_and] at hmemf
    obtain ⟨y, hy, hHy⟩ := hmemf
    exact hH (by
      simp only [blockFail, mem_filter, mem_univ, true_and]
      exact ⟨i, y, hy, hHy⟩)
  have hsome : ∀ i : Fin b,
      ((decode LT (fun y => H (i, y)) (blockEncode H x i)).1).isSome := by
    intro i
    simp [blockEncode, hblock i]
  refine Prod.ext ?_ (blockDecode_cost LT H (blockEncode H x))
  simp only [blockDecode, dif_pos hsome, Option.some.injEq]
  funext i
  have hEq : (decode LT (fun y => H (i, y)) (blockEncode H x i)).1 = some (x i) := by
    simp [blockEncode, hblock i]
  have hgen : ∀ (o : Option β) (h : o.isSome) (v : β), o = some v → o.get h = v := by
    rintro _ h v rfl; rfl
  exact hgen _ (hsome i) (x i) hEq
