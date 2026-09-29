-- Prove2me | Definitions.Def_MachineLearning_Generalization
-- name    : MachineLearning_Generalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:42:19.421157+00:00
-- url     : https://prove2.me/theorems/7c32ad0b-4c44-4712-a405-31e2f9035751
-- title:
--   Aether Catalog definitions — MachineLearning_Generalization
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Generalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Generalization.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Categorical Neural Architecture Theory. All rights reserved.
Released under Apache 2.0 license.

# Compositional Generalization Bounds from Architecture Distance

This file establishes quantitative bounds on how architectural perturbations propagate
through layer composition. The main results show that the distance between composed
networks is controlled by the sum of layer-wise distances—a functorial stability
phenomenon.

The key insight: neural architecture variation is a functorial perturbation, and
generalization error is bounded by categorical (natural transformation) distance.
This turns neural architecture search from combinatorial black art into optimization
over morphism classes with certified stability.

## Main results

* `composition_perturbation_two` — perturbation bound for two-layer composition
* `composition_perturbation_three` — perturbation bound for three-layer composition
* `layerwise_zero_implies_composition_eq` — rigidity: zero layer distance → equal compositions
* `residual_perturbation_bound` — perturbation bound specific to residual layers
* `architecture_lipschitz` — Lipschitz continuity of architecture evaluation
-/


open BigOperators Finset

/-! ## Perturbation Bounds for Composed Layers -/

/-
**Theorem 3a (Two-Layer Composition Perturbation Bound).**
    For two composed layers, the output perturbation is bounded by
    the sum of layer-wise perturbations weighted by the other layer's norm.

    This is the fundamental telescoping identity:
    b₁·b₂ - a₁·a₂ = (b₁ - a₁)·b₂ + a₁·(b₂ - a₂)

    Applied to architecture theory: changing two layers produces at most
    the sum of individual changes, weighted by the norms of the unchanged parts.
-/

/-
**Theorem 3b (Three-Layer Composition Perturbation Bound).**
    Extension to three layers: the telescoping bound gives three terms.
-/

/-
Telescoping identity for two factors.
-/

/-
Telescoping identity for three factors.
-/

/-! ## Rigidity at Zero Distance -/

/-
**Theorem 3c (Compositional Rigidity).**
    If all layer-wise distances are zero, the compositions are identical.
    This is the equality case in the generalization bound.
-/

/-
Layer-wise zero absolute difference means pointwise equality.
-/

/-
Sum of non-negative terms is zero iff each term is zero.
-/

/-! ## Architecture Distance and Lipschitz Bounds -/

/-- Architecture distance between two layer sequences: sum of absolute differences. -/
def archDistReal {k : ℕ} (a b : Fin k → ℝ) : ℝ := ∑ i, |a i - b i|

/-
Architecture distance is non-negative.
-/

/-
Architecture distance is symmetric.
-/

/-
Architecture distance satisfies the triangle inequality.
-/

/-
Architecture distance zero iff architectures are equal.
-/

/-! ## Residual Perturbation -/

/-
**Theorem 3d (Residual Perturbation Bound).**
    For residual layers `1 + f` and `1 + g`, the difference of their actions
    on a vector is controlled by `|f - g|` applied to the vector.
    Residual layers are 1-Lipschitz perturbations of the identity.
-/

/-! ## Bounds Coincide at Equality (Rigidity) -/

/-
**Theorem 3e (Bounds Rigidity).**
    When two architectures have zero distance, any upper and lower bounds on
    their performance gap must coincide. This is a rigidity theorem:
    categorical coherence (zero natural transformation distance) collapses
    the gap between upper and lower bounds.
-/


