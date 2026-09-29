-- Prove2me | Theorems.Thm_witness_lower_bound_on_variation
-- name    : witness_lower_bound_on_variation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:36:41.542059+00:00
-- url     : https://prove2.me/theorems/285b3bdb-7364-48b9-bc44-96f98d44f083
-- title:
--   Witness lower bound on variation
-- statement:
--   Formal statement of `witness_lower_bound_on_variation` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem witness_lower_bound_on_variation    {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       {n : ℕ} (hn : 0 < n)
--       (Φ : TropicalFeatureFamily X n)
--       (f : X → ℝ)
--       (a : Fin n → ℝ)
--       (w : FeaturePointWitness X)
--       (ε : ℝ) (hε : 0 ≤ ε)
--       (happrox : ∀ x : X, |f x - maxPlusEnvelope a Φ x| ≤ ε) :
--       |f w.x₁ - f w.x₂| ≤
--         2 * Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
--           (fun i => |a i|) +
--         2 * Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
--           (fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂|) +
--         2 * ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalBarronDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalBarronDuality.lean#L322

-- Thm stub generated from Bridges/TropicalBarronDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalBarronDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Barron Duality via Idempotent Choquet Features and Canonical Min-Plus Compression

This file establishes a new approximation theory for tropical neural observables,
analogous to classical Barron-space theory but genuinely idempotent: representation
by extreme tropical features, compression by sparse max-plus dictionaries, and
duality against witness/certificate functionals.

## Mathematical Overview

Classical Barron theory controls neural approximation by the variation of a representing
measure in Fourier space. In the tropical (max-plus) world, the correct analog replaces
Fourier mass with **extreme-feature idempotent variation**: the total weight needed to
represent a function as a max-plus combination of affine features.

Given a compact domain `X` and a family of "tropical features" `φ : Φ → X → ℝ`,
a tropical observable `f : X → ℝ` admits a max-plus representation:

  `f(x) ≈ sup_{φ ∈ Φ} (w(φ) + φ(x))`

The **tropical Barron norm** measures the minimal total variation of weights needed
for such representations.

## Main Results

### Theorem A: Finite-Feature Tropical Barron Representation
* `exists_fin_tropical_barron_approx` — Functions in the tropical Barron class admit
  finite max-plus approximation with variation control.

### Theorem B: Compact Choquet Envelope Approximation
* `compact_choquet_envelope_approx` — Continuous approximation by compact
  feature families with capacity variation bounds.

### Theorem C: Sparse Compression with Explicit Rate
* `sparse_tropical_compression` — Threshold-based compression with controlled error.

### Theorem D: Duality via Witness Certificates
* `witness_lower_bound_on_variation` — Witness functionals provide lower bounds
  on representation complexity.

## Cross-Domain Connections

- **Tropical geometry ↔ approximation theory**: Extreme-feature variation replaces
  Fourier mass as the complexity measure.
- **Choquet theory ↔ deep learning**: Extreme points of tropical feature hulls become
  atoms of neural layers.
- **Convex duality ↔ proof compression**: Witness certificates detecting irreducible
  feature mass certify lower bounds for both network and proof compression.
- **Idempotent analysis ↔ optimal control**: The representation
  `f(x) = sup_φ (μ(φ) + φ(x))` mirrors value-function envelopes in max-plus control.
-/

noncomputable section

open scoped NNReal Topology
open Set Filter Finset Real

/-! ## I. Core Structures: Tropical Features and Max-Plus Envelopes -/


open TropicalFeatureFamily

variable {X : Type*} [TopologicalSpace X] {n : ℕ}








/-! ## II. Fundamental Lemmas -/

/-
Tropical variation is nonneg
-/

/-
Tropical variation of the zero vector is zero
-/

/-
Tropical variation is subadditive
-/

/-
Tropical variation scales: `TV(c • a) = |c| * TV(a)`
-/

/-
Max-plus envelope with zero weights
-/

/-
Max-plus envelope is monotone in weights
-/

/-
Shifting all weights by `c` shifts the envelope by `c`
-/

/-
Max-plus envelope of a single feature
-/

/-
Max-plus envelope is 1-Lipschitz in weights (sup-norm)
-/

/-! ## III. Theorem A: Finite-Feature Tropical Barron Representation -/

/-
**Theorem A.** If `f` is in the tropical Barron class for feature family `Φ`,
    then for every `ε > 0`, there exists a weight vector achieving ε-approximation
    with controlled tropical variation.

    This is the finite tropical analog of atomic Barron representation.
-/

/-! ## IV. Sparse Compression -/


/-
The sparse approximation has controlled support size
-/

/-
Tropical variation of the sparse approximation ≤ original
-/

/-
The discarded weights have small total variation
-/

/-
**Theorem C (Sparse Tropical Compression).**
    Given an exact max-plus representation with `n` features, threshold-based
    compression produces a sparse representation with controlled error.

    The error is at most `n * threshold`, and the support size is at most `n`.
    Optimizing: choosing `threshold = V/N` gives error `n * V / N` where
    V = tropicalVariation(a).
-/

/-! ## V. Greedy Compression -/

/-
A greedy step: the feature with largest absolute weight
-/

/-! ## VI. Theorem D: Duality via Witness Certificates -/


/-
**Theorem D (Witness Lower Bound on Variation).**
    For any two test points, the oscillation of `f` between them is controlled
    by the max absolute weight times 2, plus the feature oscillation, plus 2ε.

    This gives a lower bound: any ε-approximation must have max weight at least
    `(|f(x₁) - f(x₂)| - maxFeatureOsc - 2ε) / 2`.
-/

theorem witness_lower_bound_on_variation    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {n : ℕ} (hn : 0 < n)
    (Φ : TropicalFeatureFamily X n)
    (f : X → ℝ)
    (a : Fin n → ℝ)
    (w : FeaturePointWitness X)
    (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ x : X, |f x - maxPlusEnvelope a Φ x| ≤ ε) :
    |f w.x₁ - f w.x₂| ≤
      2 * Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => |a i|) +
      2 * Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂|) +
      2 * ε := by sorry
