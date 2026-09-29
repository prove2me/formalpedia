-- Prove2me | solution 1 for AlmostLossless.card_blockGood_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:05.057909+00:00
-- url     : https://prove2.me/submissions/66a666e7-8aea-4efc-9049-b46997721d32

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_blockDecode_success
import Theorems.Thm_AlmostLossless_card_codebooks
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
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T) :
    M ^ (b * Fintype.card β) ≤ (blockGood LT x M).card + (blockFail T x M).card := by
  classical
  have hcardι : Fintype.card (Fin b × β) = b * Fintype.card β := by simp [Fintype.card_prod]
  have hsub : (blockFail T x M)ᶜ ⊆ blockGood LT x M := by
    intro H hH
    simp only [mem_compl] at hH
    have hdec := blockDecode_success hnd hmem hx hH
    simp only [blockGood, mem_filter, mem_univ, true_and, hdec]
  have h1 : ((blockFail T x M)ᶜ).card ≤ (blockGood LT x M).card := Finset.card_le_card hsub
  have hle : (blockFail T x M).card ≤ M ^ (b * Fintype.card β) := by
    have h := Finset.card_le_univ (blockFail T x M)
    rwa [card_codebooks, hcardι] at h
  have h2 : ((blockFail T x M)ᶜ).card + (blockFail T x M).card
      = M ^ (b * Fintype.card β) := by
    rw [Finset.card_compl, card_codebooks, hcardι]
    omega
  omega
