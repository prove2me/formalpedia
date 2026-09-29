-- Prove2me | solution 1 for AlmostLossless.blockDecode_success_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:25:30.414717+00:00
-- url     : https://prove2.me/submissions/eec536c0-67d8-47bc-8a9c-bae3af073095

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_blockFail_prob_le
import Theorems.Thm_AlmostLossless_card_blockGood_ge
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
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
    (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
    1 - ε ≤ ((blockGood LT x M).card : ℝ) / ((M : ℝ) ^ (b * Fintype.card β)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < (M : ℝ) ^ (b * Fintype.card β) := by positivity
  have hT1 : (1 : ℕ) ≤ T.card := hT
  have hfail : (M : ℝ) * (blockFail T x M).card
      ≤ ((b : ℝ) * ((T.card : ℝ) - 1)) * (M : ℝ) ^ (b * Fintype.card β) := by
    have h := blockFail_prob_le (M := M) T hx
    have h' : ((M * (blockFail T x M).card : ℕ) : ℝ)
        ≤ (((b * (T.card - 1)) * M ^ (b * Fintype.card β) : ℕ) : ℝ) := Nat.cast_le.2 h
    push_cast [Nat.cast_sub hT1] at h'
    exact h'
  have hgood : (M : ℝ) ^ (b * Fintype.card β) - (blockFail T x M).card
      ≤ (blockGood LT x M).card := by
    have h := card_blockGood_ge (M := M) hnd hmem hx
    have h' : ((M ^ (b * Fintype.card β) : ℕ) : ℝ)
        ≤ ((blockGood LT x M).card : ℝ) + ((blockFail T x M).card : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  have hbound : (b : ℝ) * ((T.card : ℝ) - 1) ≤ ε * M := by
    have := (div_le_iff₀ hε).1 hMe
    linarith
  have hfail2 : ((blockFail T x M).card : ℝ) ≤ ε * (M : ℝ) ^ (b * Fintype.card β) := by
    have h2 : (M : ℝ) * (blockFail T x M).card
        ≤ (M : ℝ) * (ε * (M : ℝ) ^ (b * Fintype.card β)) := by
      have h3 : ((b : ℝ) * ((T.card : ℝ) - 1)) * (M : ℝ) ^ (b * Fintype.card β)
          ≤ (ε * M) * (M : ℝ) ^ (b * Fintype.card β) :=
        mul_le_mul_of_nonneg_right hbound hpos.le
      nlinarith [hfail, h3]
    exact le_of_mul_le_mul_left h2 hMpos
  rw [le_div_iff₀ hpos]
  nlinarith [hgood, hfail2]
