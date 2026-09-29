-- Prove2me | solution 1 for AlmostLossless.length_matches_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:28:19.522317+00:00
-- url     : https://prove2.me/submissions/b417225c-8dc7-41c9-a486-7bd9a44dba3d

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Theorems.Thm_AlmostLossless_scanCost_fst
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






open AlmostLossless.ListScheme in
omit [Fintype α] in
theorem solution(h : α → Fin M) {l : List α} (hnd : l.Nodup) {x : α}
    (hx : x ∈ l) :
    ((scanCost h (h x) l).1).length
      = (collisionSet (fun _ : Fin 1 => h) 0 l.toFinset x).card + 1 := by
  classical
  rw [scanCost_fst]
  have hfilter_nodup : (l.filter (fun y => decide (h y = h x))).Nodup := hnd.filter _
  have h1 : (l.filter (fun y => decide (h y = h x))).length
      = (l.toFinset.filter (fun y => h y = h x)).card := by
    rw [← List.toFinset_card_of_nodup hfilter_nodup, List.toFinset_filter]
    simp
  rw [h1]
  have hins : l.toFinset.filter (fun y => h y = h x)
      = insert x (collisionSet (fun _ : Fin 1 => h) 0 l.toFinset x) := by
    ext y
    simp only [collisionSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase,
      List.mem_toFinset]
    constructor
    · rintro ⟨hyl, hyh⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨⟨hyx, hyl⟩, hyh⟩
    · rintro (rfl | ⟨⟨_, hyl⟩, hyh⟩)
      · exact ⟨hx, rfl⟩
      · exact ⟨hyl, hyh⟩
  rw [hins, Finset.card_insert_of_notMem (by simp [collisionSet])]
