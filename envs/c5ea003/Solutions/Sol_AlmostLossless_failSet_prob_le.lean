-- Prove2me | solution 1 for AlmostLossless.failSet_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:40.38292+00:00
-- url     : https://prove2.me/submissions/ef775733-b7e8-40bc-96d5-7c3b8c7c86c8

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_multiCollision_mul_le
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

/-- The failure event is a union of `|S| - 1` pairwise collision events. -/
theorem failSet_eq_multiCollision (S : Finset α) (x : α) :
    failSet S x M = multiCollision M ((S.erase x).image (fun y => (y, x))) := by
  ext H
  simp only [failSet, multiCollision, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨y, hy, hHy⟩
    exact ⟨(y, x), ⟨y, hy, rfl⟩, hHy⟩
  · rintro ⟨p, ⟨y, hy, rfl⟩, hHp⟩
    exact ⟨y, hy, hHp⟩





/-! ## 5. Derandomisation: a single good codebook exists -/




open AlmostLossless in
theorem solution(S : Finset α) {x : α} (hx : x ∈ S) :
    M * (failSet S x M).card ≤ (S.card - 1) * M ^ Fintype.card α := by
  classical
  rw [failSet_eq_multiCollision]
  have hpairs : ∀ p ∈ (S.erase x).image (fun y => (y, x)), p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hp
    exact (Finset.mem_erase.1 hy).1
  have hcard : ((S.erase x).image (fun y => (y, x))).card ≤ S.card - 1 := by
    have h : ((S.erase x).image (fun y => (y, x))).card ≤ (S.erase x).card :=
      Finset.card_image_le
    rwa [Finset.card_erase_of_mem hx] at h
  exact le_trans (card_multiCollision_mul_le _ hpairs) (Nat.mul_le_mul_right _ hcard)
