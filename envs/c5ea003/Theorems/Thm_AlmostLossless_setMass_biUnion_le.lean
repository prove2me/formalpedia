-- Prove2me | Theorems.Thm_AlmostLossless_setMass_biUnion_le
-- name    : AlmostLossless.setMass_biUnion_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:05:50.603949+00:00
-- url     : https://prove2.me/theorems/eef75884-7227-4450-b9c2-6f07c25848f7
-- title:
--   Subadditivity over an indexed union.
-- statement:
--   Subadditivity over an indexed union.
--
--   ```lean
--   theorem AlmostLossless.setMass_biUnion_le{ι : Type*} [DecidableEq α] (μ : FinProbDist α)
--       (s : Finset ι) (t : ι → Finset α) :
--       setMass μ (s.biUnion t) ≤ ∑ i ∈ s, setMass μ (t i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessCompression.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessCompression.lean#L67

-- Thm stub generated from Bridges/AlmostLosslessCompression.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression I: Schemes and the Relaxed Pigeonhole Bound

## Bridge: Combinatorics (pigeonhole) ↔ Probability (min-entropy) ↔ Coding theory

The exact pigeonhole bound says: a code that decodes *every* source symbol
correctly needs at least `|α|` codewords.  This file develops the *relaxed*
(almost-lossless) form of that statement:

* a scheme is an encoder/decoder pair `enc : α → Code`, `dec : Code → Option α`;
* the decoder may abstain (`none`), and may in principle err silently;
* the **success set** is the set of symbols decoded exactly.

Main results:

* `enc_injOn_successSet` / `card_successSet_le_card_code` — the exact pigeonhole
  bound applies to the success set only;
* `successMass_le` — `P(success) ≤ |Code| · p_max`, i.e. the counting bound is
  relaxed by a factor governed by the min-entropy of the source;
* `card_code_ge_of_success` — the converse: to succeed with probability `1 - ε`
  one needs `|Code| ≥ (1-ε)/p_max`;
* `log_card_code_ge_of_success` — the same statement in entropy form,
  `log |Code| ≥ H_∞(μ) + log (1-ε)`;
* `exact_decoding_pigeonhole` — the classical bound is recovered at `ε = 0`.

## Impact: certified_compression_bound, almost_lossless_converse
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

variable {α : Type*} [Fintype α]

/-! ## Section 1: Mass of a finite set of source symbols -/

theorem AlmostLossless.setMass_biUnion_le{ι : Type*} [DecidableEq α] (μ : FinProbDist α)
    (s : Finset ι) (t : ι → Finset α) :
    setMass μ (s.biUnion t) ≤ ∑ i ∈ s, setMass μ (t i) := by sorry
