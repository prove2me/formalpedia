-- Prove2me | solution 1 for AlmostLossless.exists_good_codebook
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:35:55.777293+00:00
-- url     : https://prove2.me/submissions/78ae816c-faf8-41bf-871b-d86860c82cd6

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_codebooks
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
theorem solution(S : Finset α) (hM : 0 < M) :
    ∃ H : α → Fin M, M * (badStrings S H).card ≤ S.card * (S.card - 1) := by
  classical
  set f : (α → Fin M) → ℕ := fun H => (badStrings S H).card with hf
  -- double counting: ∑_H |bad(H)| = ∑_{x ∈ S} |failSet x|
  have hswap : ∑ H : α → Fin M, f H = ∑ x ∈ S, (failSet S x M).card := by
    simp only [hf, badStrings, failSet, Finset.card_filter]
    rw [Finset.sum_comm]
  have hbound : M * ∑ H : α → Fin M, f H ≤ S.card * ((S.card - 1) * M ^ Fintype.card α) := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x ∈ S, M * (failSet S x M).card
        ≤ ∑ _x ∈ S, (S.card - 1) * M ^ Fintype.card α :=
          Finset.sum_le_sum (fun x hx => failSet_prob_le S hx)
      _ = S.card * ((S.card - 1) * M ^ Fintype.card α) := by
          rw [Finset.sum_const, smul_eq_mul]
  obtain ⟨H₀, -, hmin⟩ :=
    Finset.exists_min_image (univ : Finset (α → Fin M)) f ⟨fun _ => ⟨0, hM⟩, mem_univ _⟩
  have hsum : (M ^ Fintype.card α) * f H₀ ≤ ∑ H : α → Fin M, f H := by
    have h : ∑ _H : α → Fin M, f H₀ ≤ ∑ H : α → Fin M, f H :=
      Finset.sum_le_sum (fun H _ => hmin H (mem_univ H))
    rwa [Finset.sum_const, smul_eq_mul, Finset.card_univ, card_codebooks] at h
  refine ⟨H₀, ?_⟩
  have hpow : 0 < M ^ Fintype.card α := Nat.pow_pos hM
  have key : (M ^ Fintype.card α) * (M * f H₀)
      ≤ (M ^ Fintype.card α) * (S.card * (S.card - 1)) := by
    calc (M ^ Fintype.card α) * (M * f H₀) = M * ((M ^ Fintype.card α) * f H₀) := by ring
      _ ≤ M * ∑ H : α → Fin M, f H := Nat.mul_le_mul_left _ hsum
      _ ≤ S.card * ((S.card - 1) * M ^ Fintype.card α) := hbound
      _ = (M ^ Fintype.card α) * (S.card * (S.card - 1)) := by ring
  exact Nat.le_of_mul_le_mul_left key hpow
