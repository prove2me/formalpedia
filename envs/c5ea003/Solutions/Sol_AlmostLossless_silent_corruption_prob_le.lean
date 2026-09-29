-- Prove2me | solution 1 for AlmostLossless.silent_corruption_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:47.841898+00:00
-- url     : https://prove2.me/submissions/881653b9-53ba-45be-8953-0dc19ac8a7ba

-- Sol generated from Geometry/AlmostLosslessChecksum.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_codebooks
import Theorems.Thm_AlmostLossless_card_silentSlice_mul_le
/-
# Closing the silent-corruption loophole: a random checksum layer

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`Geometry.AlmostLosslessDecoder` proves that the scanning decoder never returns a
wrong string *provided the transmitted string is typical*.  Adversarial review
exposes the remaining loophole: an **atypical** source string `x ∉ S` can be
silently decoded to some typical `y ≠ x`, because the decoder has no way of
knowing that `x` was atypical.

Here we close that loophole with an independent random checksum
`C : α → Fin K` appended to the codeword (`log₂ K` extra bits).  The key point is
a *conditional independence* (fibrewise counting) argument: for a fixed hash
codebook `H` the candidate returned by the hash decoder is already determined,
so the checksum has only one chance in `K` of confirming it.

* `AlmostLossless.decodeChk_cost` — exact cost `|L| + 1` comparisons.
* `AlmostLossless.decodeChk_never_wrong` — typical strings are still never
  silently corrupted (deterministically).
* `AlmostLossless.silent_corruption_prob_le` — **for every source string, typical
  or not**, the probability of a silent corruption is at most `1 / K`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [DecidableEq α] {M K : ℕ}

/-! ## 1. The checksummed scheme -/






/-! ## 2. The silent-corruption probability, uniformly over all sources -/

variable [Fintype α]









open AlmostLossless in
theorem solution(L : List α) (x : α) :
    K * (silentSet L x M K).card ≤ M ^ Fintype.card α * K ^ Fintype.card α := by
  classical
  have hsub : silentSet L x M K ⊆
      (univ : Finset (α → Fin M)).biUnion (fun H => {H} ×ˢ silentSlice L x H K) := by
    intro p hp
    simp only [silentSet, mem_filter, mem_univ, true_and] at hp
    refine mem_biUnion.2 ⟨p.1, mem_univ _, ?_⟩
    rw [mem_product]
    refine ⟨by simp, ?_⟩
    simp only [silentSlice, mem_filter, mem_univ, true_and]
    exact hp
  have hcard : (silentSet L x M K).card ≤ ∑ H : α → Fin M, (silentSlice L x H K).card := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine Finset.sum_le_sum (fun H _ => ?_)
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  calc K * (silentSet L x M K).card
      ≤ K * ∑ H : α → Fin M, (silentSlice L x H K).card := Nat.mul_le_mul_left _ hcard
    _ = ∑ H : α → Fin M, K * (silentSlice L x H K).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _H : α → Fin M, K ^ Fintype.card α :=
        Finset.sum_le_sum (fun H _ => card_silentSlice_mul_le L x H)
    _ = M ^ Fintype.card α * K ^ Fintype.card α := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, card_codebooks]
