-- Prove2me | Theorems.Thm_NonArchInfoTheory_minEntropy_product_eq_add
-- name    : NonArchInfoTheory.minEntropy_product_eq_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:57:49.561409+00:00
-- url     : https://prove2.me/theorems/da68dec7-3e85-4c1f-ab3d-07db35e0c6a1
-- title:
--   H_∞(X×Y) = H_∞(X) + H_∞(Y) for independent distributions.
-- statement:
--   H_∞(X×Y) = H_∞(X) + H_∞(Y) for independent distributions.
--       Bridge: tropical ⊗ (= +) ↔ entropy additivity under independence.
--       Impact: post_quantum_security — independent key material has additive min-entropy.
--
--   ```lean
--   theorem NonArchInfoTheory.minEntropy_product_eq_add(μ : FinProbDist α) (ν : FinProbDist β) :
--       minEntropy (productDist μ ν) = minEntropy μ + minEntropy ν := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MinEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MinEntropy.lean#L273

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







/-! ## Min-Entropy Definition and Properties -/




/-! ## Deterministic Distribution -/




/-! ## Uniform Distribution Entropy -/



/-! ## Product Distribution -/

variable {β : Type*} [Fintype β] [Nonempty β]


/-
Key lemma: max of product of nonneg functions = product of maxes.
    Bridge: tropical ⊗ distributes over product spaces.
-/

theorem NonArchInfoTheory.minEntropy_product_eq_add(μ : FinProbDist α) (ν : FinProbDist β) :
    minEntropy (productDist μ ν) = minEntropy μ + minEntropy ν := by sorry
