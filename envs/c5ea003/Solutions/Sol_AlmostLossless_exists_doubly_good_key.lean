-- Prove2me | solution 1 for AlmostLossless.exists_doubly_good_key
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:10:49.996194+00:00
-- url     : https://prove2.me/submissions/ef733bd4-be94-483a-9bfa-21723adb80b3

-- Sol generated from Bridges/AlmostLosslessSharpSilent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessSharpSilent
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_card_badMass_lt
import Theorems.Thm_AlmostLossless_setMass_univ
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression VII: Silent Corruption is Rarer than Failure

## Bridge: Universal hashing (algebra) ↔ two-sided Markov counting (probability)

`exists_almost_lossless_scheme` produces a key whose *failure* probability is at
most `δ + |S|/M` and whose *silent corruption* probability is at most `|S|/M`.
That silent bound is wasteful: a silent error requires a symbol to be **outside**
the codebook (inside the codebook the decoder provably abstains rather than
lying) *and* to collide with the codebook.  The first event has probability at
most `δ`, so the first moment of the silent-error mass carries an extra factor
`δ`.

This file proves that the two guarantees can be obtained **simultaneously for a
single key**:

* `card_badMass_lt` — a Markov/counting bound: fewer than half of the keys are
  twice as bad as the average, for any region `A`;
* `exists_doubly_good_key` — a key that is good for the region `Sᶜ` *and* for
  the whole space at once (both bad sets have size `< K/2`, so they cannot
  cover the key space);
* `exists_sharp_almost_lossless_scheme` — **the deliverable**: a single explicit
  key with failure probability `≤ δ + 2|S|/M`, silent-corruption probability
  `≤ 2δ|S|/M` (a factor `δ` better), and decoding cost still exactly `|S|`.

This settles Conjecture 2 of the previous cycle's `FUTURE_DIRECTIONS.md`.

## Impact: sharp_silent_error_bound, two_sided_derandomization
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}







open AlmostLossless in
theorem solution(μ : FinProbDist α) {H : Fin K → α → Fin M}
    (hU : Universal2 H) (hK : 0 < K) (S : Finset α) :
    ∃ k : Fin K,
      (M : ℝ) * setMass μ ((Sᶜ).filter (fun x => Collides H k S x))
          ≤ 2 * (S.card : ℝ) * setMass μ Sᶜ
      ∧ (M : ℝ) * setMass μ (Finset.univ.filter (fun x => Collides H k S x))
          ≤ 2 * (S.card : ℝ) := by
  classical
  have h1 := card_badMass_lt μ hU hK S Sᶜ
  have h2 := card_badMass_lt μ hU hK S Finset.univ
  set B1 := badMassKeys μ H S Sᶜ with hB1
  set B2 := badMassKeys μ H S Finset.univ with hB2
  have hcards : ((B1 ∪ B2).card : ℝ) < K := by
    have hle : ((B1 ∪ B2).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by
      exact_mod_cast Finset.card_union_le B1 B2
    linarith
  have hne : ∃ k : Fin K, k ∉ B1 ∪ B2 := by
    by_contra hcon
    push_neg at hcon
    have hsubset : (Finset.univ : Finset (Fin K)) ⊆ B1 ∪ B2 := fun k _ => hcon k
    have : (K : ℝ) ≤ ((B1 ∪ B2).card : ℝ) := by
      have := Finset.card_le_card hsubset
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    linarith
  obtain ⟨k, hk⟩ := hne
  rw [Finset.mem_union] at hk
  push_neg at hk
  obtain ⟨hk1, hk2⟩ := hk
  simp only [hB1, badMassKeys, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt] at hk1
  simp only [hB2, badMassKeys, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt] at hk2
  refine ⟨k, by linarith [hk1], ?_⟩
  rw [setMass_univ, mul_one] at hk2
  linarith [hk2]
