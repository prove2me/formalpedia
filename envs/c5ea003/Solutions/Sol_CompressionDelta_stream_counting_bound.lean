-- Prove2me | solution 1 for CompressionDelta.stream_counting_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:49:40.392023+00:00
-- url     : https://prove2.me/submissions/70cf3463-2ca4-4470-a9d5-0a3a0d22c5d3

-- Sol generated from Tropical/CompressionDelta/Pigeonhole.lean
import Mathlib
import Definitions.Def_Tropical_CompressionDelta_Pigeonhole
import Theorems.Thm_CompressionDelta_card_shortStrings
import Theorems.Thm_CompressionDelta_mem_shortStrings

/-!
# Amortized model-delta compression, III: the counting (pigeonhole) floor

The falsifiability gate of this research thread demands *lossless* compression with the
delta counted as part of the transmitted message.  This file supplies the hard information
theoretic floor that no such scheme can cross, in a form that is agnostic about *what* the
decompressor is: the decoder may be a gzip table, a context mixer or a 16 GB pretrained
language model — only injectivity of the encoder is used.

## Main results

* `CompressionDelta.card_shortStrings` — there are exactly `2 ^ (t + 1) - 1` bitstrings of
  length at most `t` (stated without truncated subtraction).
* `CompressionDelta.card_compressible_le` — for an injective encoder, the number of
  sources whose *entire* transmission (model delta included) is at most `t` bits is at
  most `2 ^ (t + 1) - 1`; so compressible objects are exponentially rare.
* `CompressionDelta.exists_long_codeword` — the pigeonhole bound: some source must be
  transmitted in more than `t` bits as soon as there are `2 ^ (t + 1)` sources.
* `CompressionDelta.stream_counting_bound` — the streaming form: a stream of `n` messages
  from a `2 ^ s`-symbol source needs `n * s` bits for some stream, however clever the
  shared decompressor and its transmitted delta are.
-/

open CompressionDelta

open Finset

/-! ## Counting bitstrings of bounded length -/




/-! ## The counting floor for lossless codes -/

/-- **Compressible sources are exponentially rare.**  For any injective (i.e. losslessly
decodable) encoder `enc`, at most `2 ^ (t + 1) - 1` sources are transmitted in `t` bits or
fewer — no matter how large or clever the shared decompressor is, since the decompressor
is not transmitted here at all. -/
theorem card_compressible_le {α : Type*} [Fintype α] [DecidableEq α]
    (enc : α → List Bool) (hinj : Function.Injective enc) (t : ℕ) :
    ({a : α | (enc a).length ≤ t} : Set α).toFinset.card + 1 ≤ 2 ^ (t + 1) := by
  have hsub : ({a : α | (enc a).length ≤ t} : Set α).toFinset.card ≤ (shortStrings t).card := by
    refine Finset.card_le_card_of_injOn enc ?_ (fun a _ b _ h => hinj h)
    intro a ha
    simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq] at ha
    exact Finset.mem_coe.mpr ((mem_shortStrings t _).mpr ha)
  have := card_shortStrings t
  omega

/-- **Pigeonhole bound.**  With `2 ^ (t + 1)` distinct sources, any lossless encoder must
spend more than `t` bits on at least one of them.  The transmitted model delta, if any, is
part of `enc a`. -/
theorem exists_long_codeword {α : Type*} [Fintype α] [DecidableEq α]
    (enc : α → List Bool) (hinj : Function.Injective enc) (t : ℕ)
    (hcard : 2 ^ (t + 1) ≤ Fintype.card α) :
    ∃ a : α, t < (enc a).length := by
  by_contra hcon
  push_neg at hcon
  have hall : ({a : α | (enc a).length ≤ t} : Set α).toFinset = Finset.univ := by
    ext a
    simp [hcon a]
  have h := card_compressible_le enc hinj t
  rw [hall, Finset.card_univ] at h
  omega



open CompressionDelta in
theorem solution(n s : ℕ) (hs : 1 ≤ s)
    (enc : (Fin n → Fin (2 ^ s)) → List Bool) (hinj : Function.Injective enc) :
    ∃ x : Fin n → Fin (2 ^ s), n * s ≤ (enc x).length := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, by simp⟩
  have hcard : Fintype.card (Fin n → Fin (2 ^ s)) = 2 ^ (n * s) := by
    simp [← pow_mul, Nat.mul_comm]
  have hle : 2 ^ ((n * s - 1) + 1) ≤ Fintype.card (Fin n → Fin (2 ^ s)) := by
    rw [hcard]
    have : (n * s - 1) + 1 = n * s := by
      have : 1 ≤ n * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [this]
  obtain ⟨x, hx⟩ := exists_long_codeword enc hinj (n * s - 1) hle
  refine ⟨x, ?_⟩
  have : 1 ≤ n * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega
