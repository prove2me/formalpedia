-- Prove2me | Theorems.Thm_AlmostLossless_card_badKeysT_mul_le
-- name    : AlmostLossless.card_badKeysT_mul_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:06:18.327214+00:00
-- url     : https://prove2.me/theorems/3b005320-47f1-4b5d-a932-29d5419bcaec
-- title:
--   Markov step.
-- statement:
--   **Markov step.**  At most a `|S|/(T·M)` fraction of the keys give `x` more
--   than `T` collision partners — the list-decoding refinement of
--   `card_badKeys_mul_le`, which is the case `T = 1`.
--
--   ```lean
--   theorem AlmostLossless.card_badKeysT_mul_le{H : Fin K → α → Fin M} (hU : Universal2 H)
--       (S : Finset α) (x : α) (T : ℕ) :
--       (T : ℝ) * ((badKeysT H S x T).card : ℝ) * M ≤ (K : ℝ) * S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessListDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessListDecoding.lean#L156

-- Thm stub generated from Bridges/AlmostLosslessListDecoding.lean
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



omit [Fintype α] in

theorem AlmostLossless.card_badKeysT_mul_le{H : Fin K → α → Fin M} (hU : Universal2 H)
    (S : Finset α) (x : α) (T : ℕ) :
    (T : ℝ) * ((badKeysT H S x T).card : ℝ) * M ≤ (K : ℝ) * S.card := by sorry
