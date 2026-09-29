-- Prove2me | solution 1 for AlmostLossless.exists_list_almost_lossless_scheme
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:14:04.383108+00:00
-- url     : https://prove2.me/submissions/18c1a6c7-f7f5-4362-84bd-03c359f7103a

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_exists_good_key_T
import Theorems.Thm_AlmostLossless_length_matches_eq
import Theorems.Thm_AlmostLossless_listDecodeT_length_le
import Theorems.Thm_AlmostLossless_scanCost_fst
import Theorems.Thm_AlmostLossless_scanCost_snd
import Theorems.Thm_AlmostLossless_setMass_mono
import Theorems.Thm_AlmostLossless_setMass_union_le
import Theorems.Thm_AlmostLossless_setMass_univ
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression VI: List Decoding and the Rate–List Trade-off

## Bridge: Markov's inequality (probability) ↔ pigeonhole counting (combinatorics)

A list decoder answers with a short set of candidates instead of a single
symbol.  This relaxes the pigeonhole bound a second time — now by the list size
`T` rather than by the failure probability — and it *simultaneously* improves
the achievable failure probability, because a codeword only has to be discarded
when more than `T` codebook entries collide.

Main results:

* `card_listSuccessSet_le` / `list_card_code_ge_of_success` — **converse**:
  a decoder emitting lists of length `≤ T` has `P(success) ≤ T·|Code|·p_max`,
  i.e. `log|Code| + log T ≥ H_∞ + log(1−ε)`.  At `T = 1` this is the ordinary
  relaxed pigeonhole bound.
* `card_badKeysT_mul_le` — **Markov step**: at most a `|S|/(T·M)` fraction of
  keys give `x` more than `T` collision partners.
* `exists_list_almost_lossless_scheme` — **achievability**: an explicit key with
  failure probability `≤ δ + |S|/(T·M)`, decoding cost still exactly `|S|`, and
  the guarantee that a non-empty answer *always contains the true symbol*.

So list size `T` buys a factor `T` in the failure probability and costs
`log T` bits in the converse: the two sides of the trade-off match.

## Impact: list_decoding_tradeoff, no_silent_corruption
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

/-! ## Section 1: List schemes and the rate–list converse -/


variable {α : Type*} [Fintype α] [DecidableEq α] {Code : Type*}










/-! ## Section 2: The Markov step -/


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}





/-! ## Section 3: The list-decoding scheme -/


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}







/-! ## Section 4: Achievability for list decoding -/


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}






open AlmostLossless in
theorem solution(μ : FinProbDist α) {H : Fin K → α → Fin M}
    (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M) (T : ℕ) (hT : 0 < T)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter
          (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
          ≤ δ + (l.length : ℝ) / (T * M)
      ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T)
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by
  classical
  obtain ⟨k, hk⟩ := exists_good_key_T μ hU hK l.toFinset Finset.univ T
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hcard : (l.toFinset.card : ℝ) = (l.length : ℝ) := by
    rw [List.toFinset_card_of_nodup hnd]
  set C : Finset α :=
    Finset.univ.filter (fun x => T ≤ (collisionSet H k l.toFinset x).card) with hC
  have hCbound : setMass μ C ≤ (l.length : ℝ) / (T * M) := by
    rw [le_div_iff₀ (by positivity)]
    have h2 := hk
    rw [setMass_univ, mul_one, hcard] at h2
    nlinarith [h2]
  refine ⟨k, ?_, fun i => listDecodeT_length_le T _ l i, fun i => scanCost_snd _ _ _⟩
  have hsub : Finset.univ.filter (fun x => ¬ (listHashScheme T l (H k)).Succeeds x)
      ⊆ (l.toFinset)ᶜ ∪ C := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_union]
    by_cases hxl : x ∈ l.toFinset
    · right
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hlt
      push_neg at hlt
      -- few collisions ⇒ the match list is short ⇒ `x` is returned
      refine hx ?_
      have hxl' : x ∈ l := List.mem_toFinset.mp hxl
      have hlen : ((scanCost (H k) (H k x) l).1).length ≤ T := by
        have := length_matches_eq (H k) hnd hxl'
        have hcc : (collisionSet (fun _ : Fin 1 => H k) 0 l.toFinset x).card
            = (collisionSet H k l.toFinset x).card := by
          unfold collisionSet; rfl
        omega
      show x ∈ listDecodeT T (H k) l ((listHashScheme T l (H k)).enc x)
      unfold listHashScheme listDecodeT
      simp only [if_pos hlen]
      rw [scanCost_fst, List.mem_filter]
      exact ⟨hxl', by simp⟩
    · left; exact Finset.mem_compl.mpr hxl
  calc setMass μ (Finset.univ.filter (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
      ≤ setMass μ ((l.toFinset)ᶜ ∪ C) := setMass_mono μ hsub
    _ ≤ setMass μ (l.toFinset)ᶜ + setMass μ C := setMass_union_le μ _ _
    _ ≤ δ + (l.length : ℝ) / (T * M) := add_le_add hδ hCbound
