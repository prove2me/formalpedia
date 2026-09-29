-- Prove2me | Definitions.Def_Bridges_AlmostLosslessListDecoding
-- name    : Bridges_AlmostLosslessListDecoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:49.447333+00:00
-- url     : https://prove2.me/theorems/9625b275-ace7-49d1-8520-48ea6dbeeebb
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessListDecoding
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessListDecoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessListDecoding.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
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

namespace AlmostLossless

/-! ## Section 1: List schemes and the rate–list converse -/

section ListConverse

variable {α : Type*} [Fintype α] [DecidableEq α] {Code : Type*}

/-- A compression scheme whose decoder returns a *list* of candidates.  An empty
list means "I abstain". -/
structure ListScheme (α : Type*) (Code : Type*) where
  /-- The encoder. -/
  enc : α → Code
  /-- The list decoder. -/
  dec : Code → List α

/-- The list decoder succeeds when the true symbol is among the candidates. -/
def ListScheme.Succeeds (s : ListScheme α Code) (x : α) : Prop :=
  x ∈ s.dec (s.enc x)

instance (s : ListScheme α Code) : DecidablePred s.Succeeds :=
  fun _ => by unfold ListScheme.Succeeds; infer_instance

/-- The set of symbols recovered by the list decoder. -/
def listSuccessSet (s : ListScheme α Code) : Finset α :=
  Finset.univ.filter s.Succeeds


/-- Success probability of a list scheme. -/
noncomputable def listSuccessProb (μ : FinProbDist α) (s : ListScheme α Code) : ℝ :=
  setMass μ (listSuccessSet s)



end ListConverse

/-! ## Section 2: The Markov step -/

section Markov

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- Keys for which `x` has at least `T` collision partners in the codebook. -/
def badKeysT (H : Fin K → α → Fin M) (S : Finset α) (x : α) (T : ℕ) : Finset (Fin K) :=
  Finset.univ.filter (fun k => T ≤ (collisionSet H k S x).card)



end Markov

/-! ## Section 3: The list-decoding scheme -/

section ListScheme

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- The list decoder: return all codebook entries matching the codeword, unless
there are more than `T` of them, in which case abstain (empty list). -/
def listDecodeT (T : ℕ) (h : α → Fin M) (l : List α) (i : Fin M) : List α :=
  if ((scanCost h i l).1).length ≤ T then (scanCost h i l).1 else []

/-- The list-decoding compression scheme. -/
def listHashScheme (T : ℕ) (l : List α) (h : α → Fin M) : ListScheme α (Fin M) where
  enc := h
  dec := listDecodeT T h l




end ListScheme

/-! ## Section 4: Achievability for list decoding -/

section ListAchievability

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}




end ListAchievability

end AlmostLossless


