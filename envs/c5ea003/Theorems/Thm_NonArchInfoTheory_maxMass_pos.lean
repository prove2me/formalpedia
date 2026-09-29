-- Prove2me | Theorems.Thm_NonArchInfoTheory_maxMass_pos
-- name    : NonArchInfoTheory.maxMass_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:06:46.557046+00:00
-- url     : https://prove2.me/theorems/ce194b15-b46e-480a-8f8f-d0497fa0c872
-- title:
--   The maximum mass is strictly positive.
-- statement:
--   The maximum mass is strictly positive.
--
--   ```lean
--   theorem NonArchInfoTheory.maxMass_pos(μ : FinProbDist α) : 0 < maxMass μ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MinEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MinEntropy.lean#L144

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

theorem NonArchInfoTheory.maxMass_pos(μ : FinProbDist α) : 0 < maxMass μ := by sorry
