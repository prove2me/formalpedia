-- Prove2me | solution 1 for CompressionDelta.card_shortStrings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:48:31.121513+00:00
-- url     : https://prove2.me/submissions/dda42f7c-1506-4647-b44e-d90b80e94246

-- Sol generated from Tropical/CompressionDelta/Pigeonhole.lean
import Mathlib
import Definitions.Def_Tropical_CompressionDelta_Pigeonhole
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





open CompressionDelta in
theorem solution: ∀ t : ℕ, (shortStrings t).card + 1 = 2 ^ (t + 1) := by
  intro t
  induction t with
  | zero => simp [shortStrings]
  | succ t ih =>
      have hinjT : Function.Injective (fun l : List Bool => true :: l) := by
        intro a b h; simpa using h
      have hinjF : Function.Injective (fun l : List Bool => false :: l) := by
        intro a b h; simpa using h
      have hdisj : Disjoint ((shortStrings t).image (fun l => true :: l))
          ((shortStrings t).image (fun l => false :: l)) := by
        rw [Finset.disjoint_left]
        rintro a ha hb
        simp only [Finset.mem_image] at ha hb
        obtain ⟨x, _, hx⟩ := ha
        obtain ⟨y, _, hy⟩ := hb
        rw [← hx] at hy
        simp at hy
      have hnotmem : ([] : List Bool) ∉
          ((shortStrings t).image (fun l => true :: l)) ∪
            ((shortStrings t).image (fun l => false :: l)) := by
        simp
      rw [shortStrings, Finset.card_insert_of_notMem hnotmem,
        Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjT,
        Finset.card_image_of_injective _ hinjF]
      have : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
      omega
