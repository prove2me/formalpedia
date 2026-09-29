-- Prove2me | solution 1 for AlmostLossless.sum_badT_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:10:50.4793+00:00
-- url     : https://prove2.me/submissions/14f26375-2453-4ab5-afa9-f3af2ebea6d2

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_card_badKeysT_mul_le
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
    (hU : Universal2 H) (S A : Finset α) (T : ℕ) :
    (T : ℝ) * (M : ℝ) *
        ∑ k : Fin K, setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card))
      ≤ (K : ℝ) * S.card * setMass μ A := by
  classical
  have hinner : ∀ x : α,
      ∑ k : Fin K, (if T ≤ (collisionSet H k S x).card then μ.mass x else 0)
        = ((badKeysT H S x T).card : ℝ) * μ.mass x := by
    intro x
    rw [← Finset.sum_filter]
    simp [badKeysT, Finset.sum_const, nsmul_eq_mul]
  have hswap : ∑ k : Fin K,
        setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card))
      = ∑ x ∈ A, ((badKeysT H S x T).card : ℝ) * μ.mass x := by
    unfold setMass
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => hinner x
  rw [hswap, Finset.mul_sum]
  have hbound : ∀ x ∈ A, (T : ℝ) * (M : ℝ) * (((badKeysT H S x T).card : ℝ) * μ.mass x)
      ≤ ((K : ℝ) * S.card) * μ.mass x := by
    intro x _
    have h1 := card_badKeysT_mul_le hU S x T
    have h2 : (0 : ℝ) ≤ μ.mass x := μ.mass_nonneg x
    nlinarith [h1, h2]
  calc ∑ x ∈ A, (T : ℝ) * (M : ℝ) * (((badKeysT H S x T).card : ℝ) * μ.mass x)
      ≤ ∑ x ∈ A, ((K : ℝ) * S.card) * μ.mass x := Finset.sum_le_sum hbound
    _ = (K : ℝ) * S.card * setMass μ A := by rw [← Finset.mul_sum]; rfl
