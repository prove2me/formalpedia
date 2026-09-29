-- Prove2me | solution 1 for AlmostLossless.exists_sharp_almost_lossless_scheme
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:27.612523+00:00
-- url     : https://prove2.me/submissions/1aa41b0a-8f7c-4b46-9fdb-80eb057be7f3

-- Sol generated from Bridges/AlmostLosslessSharpSilent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessSharpSilent
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_collides_iff
import Theorems.Thm_AlmostLossless_exists_doubly_good_key
import Theorems.Thm_AlmostLossless_hashScheme_neverSilent_on_codebook
import Theorems.Thm_AlmostLossless_hashScheme_succeeds
import Theorems.Thm_AlmostLossless_scanCost_snd
import Theorems.Thm_AlmostLossless_setMass_mono
import Theorems.Thm_AlmostLossless_setMass_union_le
import Theorems.Thm_AlmostLossless_silentError_imp_collides
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
theorem solution(μ : FinProbDist α)
    {H : Fin K → α → Fin M} (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
          ≤ δ + 2 * (l.length : ℝ) / M
      ∧ setMass μ (Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x))
          ≤ 2 * δ * (l.length : ℝ) / M
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by
  classical
  obtain ⟨k, hsilent, hall⟩ := exists_doubly_good_key μ hU hK l.toFinset
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (l.toFinset.card : ℝ) = (l.length : ℝ) := by
    rw [List.toFinset_card_of_nodup hnd]
  refine ⟨k, ?_, ?_, fun i => scanCost_snd _ _ _⟩
  · -- failure ⊆ atypical ∪ collisions
    set C : Finset α := Finset.univ.filter (fun x => Collides H k l.toFinset x) with hC
    have hCbound : setMass μ C ≤ 2 * (l.length : ℝ) / M := by
      rw [le_div_iff₀ hMR, hcard] at *
      nlinarith [hall, hcard]
    have hsub : Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x)
        ⊆ (l.toFinset)ᶜ ∪ C := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_union]
      by_cases hxl : x ∈ l.toFinset
      · right
        rw [hC, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [collides_iff]
        by_contra hnc
        exact hx (hashScheme_succeeds hnd (List.mem_toFinset.mp hxl) hnc)
      · left; exact Finset.mem_compl.mpr hxl
    calc setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
        ≤ setMass μ ((l.toFinset)ᶜ ∪ C) := setMass_mono μ hsub
      _ ≤ setMass μ (l.toFinset)ᶜ + setMass μ C := setMass_union_le μ _ _
      _ ≤ δ + 2 * (l.length : ℝ) / M := add_le_add hδ hCbound
  · -- silent errors live outside the codebook *and* need a collision
    set D : Finset α := (l.toFinset)ᶜ.filter (fun x => Collides H k l.toFinset x)
      with hD
    have hsub : Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x) ⊆ D := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hD, Finset.mem_filter]
      refine ⟨Finset.mem_compl.mpr ?_, collides_iff.mpr (silentError_imp_collides hx)⟩
      intro hxl
      exact hashScheme_neverSilent_on_codebook (List.mem_toFinset.mp hxl) hx
    have hmass : setMass μ (l.toFinset)ᶜ ≤ δ := hδ
    have hcardnn : (0 : ℝ) ≤ (l.length : ℝ) := Nat.cast_nonneg _
    have hDb : (M : ℝ) * setMass μ D ≤ 2 * (l.length : ℝ) * δ := by
      have h1 : (M : ℝ) * setMass μ D ≤ 2 * (l.toFinset.card : ℝ) * setMass μ (l.toFinset)ᶜ :=
        hsilent
      have h2 : 2 * (l.toFinset.card : ℝ) * setMass μ (l.toFinset)ᶜ
          ≤ 2 * (l.length : ℝ) * δ := by
        rw [hcard]
        nlinarith [hmass, hcardnn]
      linarith
    have : setMass μ D ≤ 2 * δ * (l.length : ℝ) / M := by
      rw [le_div_iff₀ hMR]
      nlinarith [hDb]
    exact le_trans (setMass_mono μ hsub) this
