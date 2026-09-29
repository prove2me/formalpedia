-- Prove2me | Definitions.Def_MachineLearning_SemanticCompression
-- name    : MachineLearning_SemanticCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:31.971157+00:00
-- url     : https://prove2.me/theorems/c13be57a-89ab-4e9d-a1dd-3cfb630276fb
-- title:
--   Aether Catalog definitions — MachineLearning_SemanticCompression
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SemanticCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SemanticCompression.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semantic Compression via Tropical Information Geometry

This module formalizes the theory of meaning-preserving compression through
tropical (min-plus) algebra and idempotent projections on finite alphabets.

## Central Idea

A source distribution on a finite alphabet `α` is encoded as a weight function
`w : α → ℝ` (log-score / energy landscape). Semantic compression replaces `w`
by a nearest representative from a finite codebook `C`, where distance is
measured by the L¹ (tropical) metric.

The key insight is that compression onto a min-closed codebook is naturally
**idempotent**: the min-plus projection operator satisfies P² = P.

## Main Definitions

* `semanticDist` — L¹ distance between weight functions (tropical distortion)
* `tropicalFisher` — L¹ norm of a weight function (tropical Fisher quantity)
* `centered` — mean-centered weight function (tropical score normalization)
* `tropicalProj` — pointwise infimum projection onto a codebook
* `isSkeletonPoint` — minimal element under pointwise order in a codebook

## Main Results

* `exists_optimal_semantic_code` — existence of optimal code in a finite codebook
* `tropicalProj_mem_of_min_closed` — pointwise inf lies in a min-closed codebook
* `tropicalProj_idempotent` — tropical projection is idempotent
* `exists_idempotent_semantic_projector` — existence of idempotent semantic projector
* `semantic_dist_le_tropical_fisher_gap` — Fisher-type bound on semantic distortion
* `semantic_dist_centered_le_two_tropical_fisher` — centered distortion ≤ 2× Fisher
* `projection_semantic_error_bound` — projection error ≤ Fisher of residual

## Application Keywords

semantic compression, tropical information geometry, min-plus projection,
idempotent coding, tropical Fisher metric, semantic distortion, rate-distortion,
tropical skeleton, finite codebook optimization, geometric representation learning
-/

open Finset BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Core Definitions -/

/-- Semantic distortion: L¹ distance between weight functions on a finite alphabet.
This measures the total absolute deviation, serving as the tropical analogue
of KL-divergence in the min-plus regime. -/
def semanticDist (w v : α → ℝ) : ℝ :=
  ∑ a, |w a - v a|

/-- Tropical Fisher quantity: L¹ norm of a weight function.
This serves as a finite-dimensional surrogate for the Fisher information metric,
measuring the total energy/score magnitude. -/
def tropicalFisher (w : α → ℝ) : ℝ :=
  ∑ a, |w a|

/-- Centered (mean-normalized) weight function. Subtracts the mean score,
producing a zero-mean representative of the same semantic equivalence class. -/
def centered (w : α → ℝ) : α → ℝ :=
  fun a => w a - ((∑ b, w b) / Fintype.card α)

/-- Tropical projection: pointwise infimum over a finite codebook.
For each symbol `a`, takes the minimum score across all codewords.
This is the canonical min-plus projection operator. -/
def tropicalProj (C : Finset (α → ℝ)) (hne : C.Nonempty) (_w : α → ℝ) : α → ℝ :=
  fun a => C.inf' hne (fun v => v a)


/-! ## Theorem 1: Existence of Optimal Semantic Code -/

/-
Every source has a nearest semantic code in a nonempty finite codebook.
This is the foundational existence result for semantic compression:
the finite argmin over the codebook always yields an optimal representative.

This connects to rate-distortion theory: the optimal code exists and is
computable by exhaustive search over the finite codebook.
-/

/-! ## Theorem 2: Idempotent Tropical Projection -/

/-
The pointwise infimum of a min-closed codebook lies in the codebook.
This is the key structural lemma: min-closure ensures the tropical projection
remains within the semantic model class.
-/

/-
Tropical projection is idempotent on min-closed codebooks.
Once a weight function has been projected onto the codebook, projecting
again yields the same result. This is the operator-theoretic core of
semantic compression: P² = P.

In categorical language, this makes the projection a reflector onto
the semantic subspace. In learning theory, it defines a canonical
semantic bottleneck.
-/

/-
There exists an idempotent semantic projector for any nonempty codebook.
This is the existential formulation: we construct a function P from weight
functions to codewords such that P² = P and P always lands in the codebook.
-/

/-! ## Theorem 3: Tropical Fisher-Type Bounds -/

/-
The semantic distance equals the tropical Fisher quantity of the difference.
This is the fundamental identity connecting L¹ distortion to the Fisher metric.
-/

/-
Semantic distance is bounded by the tropical Fisher quantity of the difference.
This is a direct corollary of the equality, included for API convenience.
-/

/-
Key lemma: the L¹ norm of a centered vector is at most twice the original.
For any function d and its mean μ, ∑|d(a) - μ| ≤ 2·∑|d(a)|.
-/

/-
Centered semantic distortion is at most twice the tropical Fisher quantity.
Centering (subtracting the mean) is a gauge normalization that preserves
semantic content. The factor of 2 comes from the triangle inequality through
the mean. This is the tropical analogue of a Cramér-Rao type bound:
the centered distortion is geometrically controlled.
-/

/-
The projection error is bounded by the tropical Fisher quantity of the residual.
This is the geometric certificate for semantic loss: the Fisher-type quantity
acts as an upper bound on the compression error.
-/

/-! ## Additional Properties -/

/-
Semantic distance is nonnegative.
-/

/-
Semantic distance is symmetric.
-/

/-
Semantic distance satisfies the triangle inequality.
-/

/-
Tropical Fisher is nonnegative.
-/

end


