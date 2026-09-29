-- Prove2me | solution 1 for AlmostLossless.card_badKeysT_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:01:16.076232+00:00
-- url     : https://prove2.me/submissions/72a8b847-7d5f-46e5-9e29-fa6e17ffd5ff

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Theorems.Thm_AlmostLossless_sum_card_collisionSet_mul_le
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
    (S : Finset α) (x : α) (T : ℕ) :
    (T : ℝ) * ((badKeysT H S x T).card : ℝ) * M ≤ (K : ℝ) * S.card := by
  classical
  have hstep : (T : ℝ) * ((badKeysT H S x T).card : ℝ)
      ≤ ∑ k : Fin K, ((collisionSet H k S x).card : ℝ) := by
    calc (T : ℝ) * ((badKeysT H S x T).card : ℝ)
        = ∑ _k ∈ badKeysT H S x T, (T : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ k ∈ badKeysT H S x T, ((collisionSet H k S x).card : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          simp only [badKeysT, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact_mod_cast hk
      _ ≤ ∑ k : Fin K, ((collisionSet H k S x).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => Nat.cast_nonneg _)
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  calc (T : ℝ) * ((badKeysT H S x T).card : ℝ) * M
      ≤ (∑ k : Fin K, ((collisionSet H k S x).card : ℝ)) * M :=
        mul_le_mul_of_nonneg_right hstep hM
    _ ≤ (K : ℝ) * S.card := sum_card_collisionSet_mul_le hU S x
