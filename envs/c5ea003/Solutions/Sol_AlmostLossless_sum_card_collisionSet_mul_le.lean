-- Prove2me | solution 1 for AlmostLossless.sum_card_collisionSet_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:59:41.552982+00:00
-- url     : https://prove2.me/submissions/62287efe-64ae-43dc-bc06-071ec779652f

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
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
omit [Fintype α] in
theorem solution{H : Fin K → α → Fin M} (hU : Universal2 H)
    (S : Finset α) (x : α) :
    (∑ k : Fin K, ((collisionSet H k S x).card : ℝ)) * M ≤ (K : ℝ) * S.card := by
  classical
  have hswap : ∑ k : Fin K, ((collisionSet H k S x).card : ℝ)
      = ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) := by
    have h1 : ∀ k : Fin K, ((collisionSet H k S x).card : ℝ)
        = ∑ y ∈ S.erase x, (if H k y = H k x then (1 : ℝ) else 0) := by
      intro k
      rw [← Finset.sum_filter]
      simp [collisionSet, Finset.sum_const]
    have h2 : ∀ y : α, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ)
        = ∑ k : Fin K, (if H k y = H k x then (1 : ℝ) else 0) := by
      intro y
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]
    simp_rw [h1, h2]
    rw [Finset.sum_comm]
  rw [hswap, Finset.sum_mul]
  calc ∑ y ∈ S.erase x, ((Finset.univ.filter (fun k => H k y = H k x)).card : ℝ) * M
      ≤ ∑ _y ∈ S.erase x, (K : ℝ) :=
        Finset.sum_le_sum fun y hy => hU y x (Finset.mem_erase.mp hy).1
    _ = ((S.erase x).card : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) * K := by
        have : ((S.erase x).card : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg K)
    _ = (K : ℝ) * S.card := by ring
