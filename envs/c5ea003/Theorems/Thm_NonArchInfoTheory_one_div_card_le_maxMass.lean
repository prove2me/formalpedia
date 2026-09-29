-- Prove2me | Theorems.Thm_NonArchInfoTheory_one_div_card_le_maxMass
-- name    : NonArchInfoTheory.one_div_card_le_maxMass
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:57:40.180635+00:00
-- url     : https://prove2.me/theorems/cb8cd544-3b00-48f2-9fbd-a39bb70ab107
-- title:
--   Lower bound: max mass ≥ 1/|α| (pigeonhole / averaging argument).
-- statement:
--   Lower bound: max mass ≥ 1/|α| (pigeonhole / averaging argument).
--       Impact: certified_robustness — worst-case probability lower bound.
--
--   ```lean
--   theorem NonArchInfoTheory.one_div_card_le_maxMass(μ : FinProbDist α) :
--       1 / (Fintype.card α : ℝ) ≤ maxMass μ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MinEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MinEntropy.lean#L157

-- Thm stub generated from Bridges/MinEntropy.lean
import Mathlib
import Definitions.Def_Bridges_MinEntropy
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Non-Archimedean Information Theory: Min-Entropy Foundations

## Bridge: Tropical Algebra ↔ Cryptographic Entropy ↔ Idempotent Analysis

Min-entropy H_∞(X) = -log(max_x p(x)) is simultaneously:
- The natural entropy of the tropical (min-plus) semifield (ℝ ∪ {∞}, min, +)
- The fundamental resource for cryptographic randomness extraction
- The worst-case measure for post-quantum security analysis

## Impact: post_quantum_security, certified_robustness, tropical_hash_collision
-/


open Finset Real BigOperators

open NonArchInfoTheory


variable {α : Type*} [Fintype α]



/-! ## Total Variation Distance

These results don't require `Nonempty α`, so we prove them before
introducing that variable. -/


variable {α : Type*} [Fintype α]








/-! ## Uniform Distribution -/




/-! ## Maximum Mass -/

variable [Nonempty α]

theorem NonArchInfoTheory.one_div_card_le_maxMass(μ : FinProbDist α) :
    1 / (Fintype.card α : ℝ) ≤ maxMass μ := by sorry
