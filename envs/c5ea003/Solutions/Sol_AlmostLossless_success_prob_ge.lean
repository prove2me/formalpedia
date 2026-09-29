-- Prove2me | solution 1 for AlmostLossless.success_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:48.591854+00:00
-- url     : https://prove2.me/submissions/1834c2ba-233e-4d5d-9229-6fe5fb4e362f

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_goodSet_ge
import Theorems.Thm_AlmostLossless_failSet_prob_le
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
    (hmem : ∀ y, y ∈ L ↔ y ∈ S) {x : α} (hx : x ∈ S) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) (hMe : ((S.card : ℝ) - 1) / ε ≤ M) :
    1 - ε ≤ ((goodSet L x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by
  have hpos : (0 : ℝ) < (M : ℝ) ^ Fintype.card α := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  have hScard : (1 : ℕ) ≤ S.card := Finset.card_pos.2 ⟨x, hx⟩
  have hfail : (M : ℝ) * (failSet S x M).card
      ≤ ((S.card : ℝ) - 1) * (M : ℝ) ^ Fintype.card α := by
    have h := failSet_prob_le (M := M) S hx
    have h' : ((M * (failSet S x M).card : ℕ) : ℝ)
        ≤ (((S.card - 1) * M ^ Fintype.card α : ℕ) : ℝ) := Nat.cast_le.2 h
    push_cast [Nat.cast_sub hScard] at h'
    exact h'
  have hgood : (M : ℝ) ^ Fintype.card α - (failSet S x M).card ≤ (goodSet L x M).card := by
    have h := card_goodSet_ge (M := M) hnd hmem hx
    have h' : ((M ^ Fintype.card α : ℕ) : ℝ)
        ≤ ((goodSet L x M).card : ℝ) + ((failSet S x M).card : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hbound : ((S.card : ℝ) - 1) ≤ ε * M := by
    have := (div_le_iff₀ hε).1 hMe
    linarith
  have hfail2 : ((failSet S x M).card : ℝ) ≤ ε * (M : ℝ) ^ Fintype.card α := by
    have h2 : (M : ℝ) * (failSet S x M).card ≤ (M : ℝ) * (ε * (M : ℝ) ^ Fintype.card α) := by
      have h3 : ((S.card : ℝ) - 1) * (M : ℝ) ^ Fintype.card α
          ≤ (ε * M) * (M : ℝ) ^ Fintype.card α :=
        mul_le_mul_of_nonneg_right hbound hpos.le
      nlinarith [hfail, h3]
    exact le_of_mul_le_mul_left h2 hMpos
  rw [le_div_iff₀ hpos]
  nlinarith [hgood, hfail2]
