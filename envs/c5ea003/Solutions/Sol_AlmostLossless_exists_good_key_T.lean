-- Prove2me | solution 1 for AlmostLossless.exists_good_key_T
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:12:33.249101+00:00
-- url     : https://prove2.me/submissions/3a4aa217-7116-49d8-84ae-38899a771bd9

-- Sol generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_sum_badT_mass_le
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
    (hU : Universal2 H) (hK : 0 < K) (S A : Finset α) (T : ℕ) :
    ∃ k : Fin K, (T : ℝ) * (M : ℝ) *
        setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card))
      ≤ (S.card : ℝ) * setMass μ A := by
  classical
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := by
    have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    exact Finset.univ_nonempty
  have hR : ∑ _k : Fin K, ((S.card : ℝ) * setMass μ A)
      = (K : ℝ) * S.card * setMass μ A := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum : ∑ k : Fin K, ((T : ℝ) * (M : ℝ) *
        setMass μ (A.filter (fun x => T ≤ (collisionSet H k S x).card)))
      ≤ ∑ _k : Fin K, ((S.card : ℝ) * setMass μ A) := by
    rw [← Finset.mul_sum, hR]
    exact sum_badT_mass_le μ hU S A T
  obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨k, hk⟩
