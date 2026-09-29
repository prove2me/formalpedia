-- Prove2me | Theorems.Thm_NonArchInfoTheory_totalVariation_eq_zero_iff
-- name    : NonArchInfoTheory.totalVariation_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:58:05.39663+00:00
-- url     : https://prove2.me/theorems/bcec551d-18bb-4cb8-ae49-cdeff3dbaca9
-- title:
--   Total variation distance is zero iff distributions are equal.
-- statement:
--   Total variation distance is zero iff distributions are equal.
--
--   ```lean
--   theorem NonArchInfoTheory.totalVariation_eq_zero_iff(μ ν : FinProbDist α) :
--       totalVariation μ ν = 0 ↔ μ = ν := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MinEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MinEntropy.lean#L72

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

theorem NonArchInfoTheory.totalVariation_eq_zero_iff(μ ν : FinProbDist α) :
    totalVariation μ ν = 0 ↔ μ = ν := by sorry
