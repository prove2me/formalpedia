-- Prove2me | solution 1 for AlmostLossless.card_goodSet_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:30:52.54668+00:00
-- url     : https://prove2.me/submissions/967ed899-bcab-42c2-bcb8-2ba8eb2bcb2a

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_codebooks
import Theorems.Thm_AlmostLossless_decode_success_of_not_mem_failSet
/-
# Almost-lossless compression: an explicit decoder, its cost, and its failure probability

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The scheme.  Fix a *typical set* `S : Finset α` (the strings the source actually
produces with high probability), enumerated as a duplicate-free candidate list
`L`, and a codebook `H : α → Fin M` drawn uniformly at random.  The encoder sends
`H x` (`⌈log₂ M⌉` bits).  The decoder scans `L`, collects all `y` with
`H y = H x`, and

* outputs `some y` **only** when that list is a singleton, and
* outputs `none` otherwise.

Main results:

* `AlmostLossless.decode_cost` — the decoder performs **exactly `|L|`** hash
  comparisons (an exact complexity figure, not an asymptotic one).
* `AlmostLossless.decode_never_wrong` — *no silent corruption*: whenever the
  decoder outputs a string, that string is the transmitted one.  Errors are
  always reported as `none`.
* `AlmostLossless.decode_success_of_not_mem_failSet` — the decoder succeeds
  unless the codebook collides on the typical set.
* `AlmostLossless.failSet_prob_le` / `AlmostLossless.success_prob_ge` — the
  Shannon random-coding bound in exact counting form and in ℝ:
  `P[failure] ≤ (|S| - 1)/M`, hence `P[success] ≥ 1 - ε` as soon as
  `M ≥ (|S| - 1)/ε`.
* `AlmostLossless.exists_good_codebook` — derandomisation: some *fixed*
  codebook of size `M` fails on at most `|S|(|S|-1)/M` typical strings.
-/

open AlmostLossless

open Finset

/-! ## 1. The scanning decoder and its exact cost -/

variable {α : Type*} [DecidableEq α] {M : ℕ}







/-! ## 2. No silent corruption -/



/-! ## 3. When does the decoder succeed? -/

variable [Fintype α]



/-! ## 4. The random-coding bound -/






/-! ## 5. Derandomisation: a single good codebook exists -/




open AlmostLossless in
theorem solution{S : Finset α} {L : List α} (hnd : L.Nodup)
    (hmem : ∀ y, y ∈ L ↔ y ∈ S) {x : α} (hx : x ∈ S) :
    M ^ Fintype.card α ≤ (goodSet L x M).card + (failSet S x M).card := by
  classical
  have hsub : (failSet S x M)ᶜ ⊆ goodSet L x M := by
    intro H hH
    simp only [mem_compl] at hH
    have hdec := decode_success_of_not_mem_failSet hnd hmem hx hH
    simp only [goodSet, mem_filter, mem_univ, true_and, hdec]
  have h1 : ((failSet S x M)ᶜ).card ≤ (goodSet L x M).card := Finset.card_le_card hsub
  have hle : (failSet S x M).card ≤ M ^ Fintype.card α := by
    have h := Finset.card_le_univ (failSet S x M)
    simpa [Finset.card_univ, card_codebooks] using h
  have h2 : ((failSet S x M)ᶜ).card + (failSet S x M).card = M ^ Fintype.card α := by
    rw [Finset.card_compl, card_codebooks]
    omega
  omega
