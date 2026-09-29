-- Prove2me | solution 1 for AlmostLossless.blockFail_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:16:47.931552+00:00
-- url     : https://prove2.me/submissions/f0bb1c36-c056-4441-b85c-1611ca4be28d

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_multiCollision_mul_le
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

/-- The blocked failure event is contained in a union of `b (|T| - 1)` pairwise
collision events. -/
theorem blockFail_subset (T : Finset β) (x : Fin b → β) :
    blockFail T x M ⊆
      multiCollision M ((univ : Finset (Fin b)).biUnion
        (fun i => (T.erase (x i)).image (fun y => ((i, y), (i, x i))))) := by
  intro H hH
  simp only [blockFail, mem_filter, mem_univ, true_and] at hH
  obtain ⟨i, y, hy, hHy⟩ := hH
  simp only [multiCollision, mem_filter, mem_univ, true_and]
  exact ⟨((i, y), (i, x i)), mem_biUnion.2 ⟨i, mem_univ i, mem_image.2 ⟨y, hy, rfl⟩⟩, hHy⟩





/-! ## 5. The complexity separation -/


  


open AlmostLossless in
theorem solution(T : Finset β) {x : Fin b → β} (hx : ∀ i, x i ∈ T) :
    M * (blockFail T x M).card ≤ (b * (T.card - 1)) * M ^ (b * Fintype.card β) := by
  classical
  set P : Finset ((Fin b × β) × (Fin b × β)) :=
    (univ : Finset (Fin b)).biUnion
      (fun i => (T.erase (x i)).image (fun y => ((i, y), (i, x i)))) with hP
  have hpairs : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    rw [hP, mem_biUnion] at hp
    obtain ⟨i, -, hi⟩ := hp
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hi
    have : y ≠ x i := (Finset.mem_erase.1 hy).1
    simpa using this
  have hPcard : P.card ≤ b * (T.card - 1) := by
    have h1 : P.card ≤ ∑ i : Fin b, ((T.erase (x i)).image
        (fun y => ((i, y), (i, x i)))).card := by
      rw [hP]; exact Finset.card_biUnion_le
    have h2 : ∀ i : Fin b, ((T.erase (x i)).image (fun y => ((i, y), (i, x i)))).card
        ≤ T.card - 1 := by
      intro i
      have h := Finset.card_image_le (s := T.erase (x i))
        (f := fun y => ((i, y), (i, x i)))
      rwa [Finset.card_erase_of_mem (hx i)] at h
    calc P.card ≤ ∑ i : Fin b, ((T.erase (x i)).image
            (fun y => ((i, y), (i, x i)))).card := h1
      _ ≤ ∑ _i : Fin b, (T.card - 1) := Finset.sum_le_sum (fun i _ => h2 i)
      _ = b * (T.card - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hcardι : Fintype.card (Fin b × β) = b * Fintype.card β := by
    simp [Fintype.card_prod]
  calc M * (blockFail T x M).card
      ≤ M * (multiCollision M P).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card (blockFail_subset T x))
    _ ≤ P.card * M ^ Fintype.card (Fin b × β) := card_multiCollision_mul_le P hpairs
    _ ≤ (b * (T.card - 1)) * M ^ (b * Fintype.card β) := by
        rw [hcardι]; exact Nat.mul_le_mul_right _ hPcard
