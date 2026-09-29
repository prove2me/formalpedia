-- Prove2me | Theorems.Thm_AlmostLossless_exists_list_almost_lossless_scheme
-- name    : AlmostLossless.exists_list_almost_lossless_scheme
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:07:50.292757+00:00
-- url     : https://prove2.me/theorems/643113dc-a05c-4478-8cca-5ad127927bf9
-- title:
--   List-decoding achievability.
-- statement:
--   **List-decoding achievability.**  With list size `T ≥ 1`, an explicit key of
--   the universal family gives a scheme that
--
--   fails with probability at most `δ + |l|/(T·M)` — a factor `T` better than the
--     unique-decoding bound `δ + |l|/M`;
--   never misleads: a non-empty answer always contains the true symbol
--     (`listDecodeT_contains_of_ne_nil`);
--   returns at most `T` candidates and still costs exactly `|l|` steps.
--
--   ```lean
--   theorem AlmostLossless.exists_list_almost_lossless_scheme(μ : FinProbDist α) {H : Fin K → α → Fin M}
--       (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M) (T : ℕ) (hT : 0 < T)
--       (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
--       ∃ k : Fin K,
--         setMass μ (Finset.univ.filter
--             (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
--             ≤ δ + (l.length : ℝ) / (T * M)
--         ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T)
--         ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessListDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessListDecoding.lean#L314

-- Thm stub generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
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

theorem AlmostLossless.exists_list_almost_lossless_scheme(μ : FinProbDist α) {H : Fin K → α → Fin M}
    (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M) (T : ℕ) (hT : 0 < T)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter
          (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
          ≤ δ + (l.length : ℝ) / (T * M)
      ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T)
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by sorry
