-- Prove2me | Definitions.Def_Bridges_TropicalBarronDuality
-- name    : Bridges_TropicalBarronDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:53.155975+00:00
-- url     : https://prove2.me/theorems/c0292950-a7b8-4373-8c2a-d2cf3ab39ab0
-- title:
--   Aether Catalog definitions — Bridges_TropicalBarronDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalBarronDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalBarronDuality.lean by skeleton subtraction
import Mathlib
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

/-- A `TropicalFeatureFamily` packages a finite family of continuous real-valued
    features on a topological space, indexed by `Fin n`. -/
structure TropicalFeatureFamily (X : Type*) [TopologicalSpace X] (n : ℕ) where
  /-- The family of continuous features -/
  features : Fin n → C(X, ℝ)

namespace TropicalFeatureFamily

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- Evaluate the i-th feature at a point x -/
def eval (Φ : TropicalFeatureFamily X n) (i : Fin n) (x : X) : ℝ :=
  Φ.features i x


end TropicalFeatureFamily

/-- The **max-plus envelope** of weights `a : Fin n → ℝ` and features `Φ`:
    `(maxPlusEnvelope a Φ)(x) = sup_i (a_i + φ_i(x))`

    When `n = 0`, the envelope is the constant function `0`. -/
def maxPlusEnvelope {X : Type*} [TopologicalSpace X] {n : ℕ}
    (a : Fin n → ℝ) (Φ : TropicalFeatureFamily X n) (x : X) : ℝ :=
  if h : 0 < n then
    Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun i => a i + Φ.eval i x)
  else 0

/-- The **tropical variation** of a coefficient vector: `∑ |a_i|`. -/
def tropicalVariation {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |a i|

/-- The **tropical Barron norm** of `f` w.r.t. feature family `Φ` at tolerance `ε`:
    the infimum of tropical variation over all ε-approximating weight vectors. -/
def TropicalBarronNorm {X : Type*} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (Φ : TropicalFeatureFamily X n) (f : X → ℝ) (ε : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ a : Fin n → ℝ,
    tropicalVariation a = v ∧
    ∀ x : X, |f x - maxPlusEnvelope a Φ x| ≤ ε }

/-- A function `f` is in the **tropical Barron class** if for every `ε > 0`,
    there exists an ε-approximating max-plus envelope with finite variation. -/
def InTropicalBarronClass {X : Type*} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (Φ : TropicalFeatureFamily X n) (f : X → ℝ) : Prop :=
  ∀ ε > 0, ∃ a : Fin n → ℝ, ∀ x : X, |f x - maxPlusEnvelope a Φ x| ≤ ε

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

/-- Sparse approximation by zeroing small weights -/
def sparseApprox {n : ℕ} (a : Fin n → ℝ) (threshold : ℝ) : Fin n → ℝ :=
  fun i => if |a i| ≥ threshold then a i else 0

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

/-- A **feature-point witness** is a pair of test points in `X`. -/
structure FeaturePointWitness (X : Type*) where
  x₁ : X
  x₂ : X

/-
**Theorem D (Witness Lower Bound on Variation).**
    For any two test points, the oscillation of `f` between them is controlled
    by the max absolute weight times 2, plus the feature oscillation, plus 2ε.

    This gives a lower bound: any ε-approximation must have max weight at least
    `(|f(x₁) - f(x₂)| - maxFeatureOsc - 2ε) / 2`.
-/

/-
**Witness lower bound on total variation.**
    Any ε-approximation must have total variation at least as large as the
    best single-feature approximation error minus ε.
-/

/-! ## VII. Tropical Barron Norm Properties -/

/-
The Barron norm is nonincreasing in ε, provided the Barron class at ε₁ is nonempty.
    (When the infimum set is empty, `sInf ∅ = 0` by convention, which
    breaks monotonicity.)
-/

/-! ## VIII. Compact Feature Space: Choquet Envelope -/

/-- A **compact tropical feature system**: compact feature space with
    jointly continuous evaluation. -/
structure CompactTropicalFeatureSystem (X : Type*) (Φ : Type*)
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Φ] [CompactSpace Φ] where
  eval : Φ → X → ℝ
  continuous_eval : Continuous (Function.uncurry eval)

variable {X Φ : Type*}
  [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Φ] [CompactSpace Φ]

/-
Each feature in a compact system is continuous
-/

/-
The evaluation is bounded on the compact product
-/

/-- An **atomic capacity** assigns weights to finitely many features. -/
structure AtomicCapacity (Φ : Type*) where
  support : Finset Φ
  weight : Φ → ℝ
  weight_support : ∀ φ, φ ∉ support → weight φ = 0

/-- Total variation of an atomic capacity -/
def AtomicCapacity.totalVariation {Φ : Type*} (μ : AtomicCapacity Φ) : ℝ :=
  μ.support.sum (fun φ => |μ.weight φ|)

/-- The max-plus integral of an atomic capacity -/
def AtomicCapacity.tropIntegral
    {X Φ : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Φ] [CompactSpace Φ]
    (μ : AtomicCapacity Φ) (eval : Φ → X → ℝ) (x : X) : ℝ :=
  if h : μ.support.Nonempty then
    μ.support.sup' h (fun φ => μ.weight φ + eval φ x)
  else 0

/-
Total variation of an atomic capacity is nonneg
-/

/-
**Theorem B (Compact Choquet Envelope Approximation).**
    Given a finite ε-approximation by features from a compact system,
    there exists an atomic capacity achieving the same approximation
    with controlled total variation.
-/

/-! ## IX. Closure Properties of the Tropical Barron Class -/

/-- Max-plus combination of two functions -/
def tropicalMax {X : Type*} (f g : X → ℝ) : X → ℝ := fun x => max (f x) (g x)

/-- Translation of a function -/
def tropicalShift {X : Type*} (f : X → ℝ) (c : ℝ) : X → ℝ := fun x => f x + c

/-
The Barron class is closed under `max`
-/

/-
The Barron class is closed under translation (requires at least one feature,
    since for `n = 0` the max-plus envelope is always `0` and cannot represent
    nonzero constants).
-/

/-
Every single feature is in the Barron class
-/

/-
Every max-plus envelope is in the Barron class of its feature family
-/

end


