-- Prove2me | solution 1 for AlmostLossless.card_badMass_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:05:22.635444+00:00
-- url     : https://prove2.me/submissions/ebd0f7a6-3da9-49b9-94bd-daa4c8ce3f00

-- Sol generated from Bridges/AlmostLosslessSharpSilent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessSharpSilent
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_setMass_nonneg
import Theorems.Thm_AlmostLossless_sum_collision_mass_le
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
    (hU : Universal2 H) (hK : 0 < K) (S A : Finset α) :
    ((badMassKeys μ H S A).card : ℝ) * 2 < K := by
  classical
  set f : Fin K → ℝ :=
    fun k => (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x)) with hf
  have hfnonneg : ∀ k, 0 ≤ f k := fun k =>
    mul_nonneg (Nat.cast_nonneg M) (setMass_nonneg _ _)
  set c : ℝ := (S.card : ℝ) * setMass μ A with hc
  have hcnonneg : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (setMass_nonneg _ _)
  have hsum : ∑ k : Fin K, f k ≤ (K : ℝ) * c := by
    have := sum_collision_mass_le μ hU S A
    rw [hf, ← Finset.mul_sum]
    rw [hc]
    calc (M : ℝ) * ∑ k : Fin K, setMass μ (A.filter (fun x => Collides H k S x))
        ≤ (K : ℝ) * S.card * setMass μ A := this
      _ = (K : ℝ) * ((S.card : ℝ) * setMass μ A) := by ring
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rcases eq_or_lt_of_le hcnonneg with hc0 | hcpos
  · -- average zero: no bad keys at all
    have hempty : badMassKeys μ H S A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      simp only [badMassKeys, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hle : f k ≤ ∑ j : Fin K, f j :=
        Finset.single_le_sum (fun j _ => hfnonneg j) (Finset.mem_univ k)
      have hKc : (K : ℝ) * c = 0 := by rw [← hc0]; ring
      have hfk : f k ≤ 0 := by linarith [hle, hsum, hKc]
      have hck : 2 * c < f k := by rw [hc, hf]; exact hk
      linarith
    rw [hempty]
    simpa using hKR
  · -- genuine Markov argument
    set B := badMassKeys μ H S A with hB
    rcases Finset.eq_empty_or_nonempty B with hBe | hBne
    · rw [hBe]; simpa using hKR
    · have hlow : ∑ k ∈ B, (2 * c) < ∑ k ∈ B, f k := by
        refine Finset.sum_lt_sum_of_nonempty hBne ?_
        intro k hk
        rw [hB, badMassKeys, Finset.mem_filter] at hk
        exact hk.2
      have hsub : ∑ k ∈ B, f k ≤ ∑ k : Fin K, f k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun j _ _ => hfnonneg j)
      have hconst : ∑ _k ∈ B, (2 * c) = (B.card : ℝ) * (2 * c) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have : (B.card : ℝ) * (2 * c) < (K : ℝ) * c := by
        rw [← hconst]; linarith
      nlinarith [this, hcpos]
