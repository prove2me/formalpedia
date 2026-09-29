-- Prove2me | solution 1 for witness_lower_bound_on_variation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:28:35.717163+00:00
-- url     : https://prove2.me/submissions/9e754b28-b3c3-4282-9c25-0765fccf15cb

-- Sol generated from Bridges/TropicalBarronDuality.lean
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


variable {X Φ : Type*}
  [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Φ] [CompactSpace Φ]

/-
Each feature in a compact system is continuous
-/

/-
The evaluation is bounded on the compact product
-/




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


theorem solution    {X : Type*} [TopologicalSpace X] [CompactSpace X]
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
      2 * ε := by
  -- By definition of maxPlusEnvelope, we have:
  have h_maxPlusEnvelope : ∀ x, maxPlusEnvelope a Φ x = Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => a i + Φ.eval i x) := by
    unfold maxPlusEnvelope; aesop;
  -- Applying the triangle inequality to the difference of the maxPlusEnvelopes:
  have h_triangle : |maxPlusEnvelope a Φ w.x₁ - maxPlusEnvelope a Φ w.x₂| ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂|) := by
    have h_triangle : ∀ i, |(a i + Φ.eval i w.x₁) - (a i + Φ.eval i w.x₂)| ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂|) := by
      exact fun i => by simpa [ add_sub_add_left_eq_sub ] using Finset.le_sup' ( fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂| ) ( Finset.mem_univ i ) ;
    simp_all +decide [ abs_le ];
    obtain ⟨ b, hb₁, hb₂ ⟩ := Finset.exists_max_image Finset.univ ( fun i => |Φ.eval i w.x₁ - Φ.eval i w.x₂| ) ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩ ; use b; simp_all +decide [ Finset.sup'_le_iff ] ;
    constructor <;> intro i <;> obtain ⟨ j, hj₁, hj₂ ⟩ := h_triangle i <;> linarith [ Finset.le_sup' ( fun i => a i + Φ.eval i w.x₁ ) ( Finset.mem_univ i ), Finset.le_sup' ( fun i => a i + Φ.eval i w.x₂ ) ( Finset.mem_univ i ), abs_le.mp ( hb₂ i ), abs_le.mp ( hb₂ j ) ] ;
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩ <;> linarith [ abs_le.mp ( happrox w.x₁ ), abs_le.mp ( happrox w.x₂ ), abs_le.mp h_triangle, show ( 0 : ℝ ) ≤ Finset.univ.sup' ( Finset.univ_nonempty_iff.mpr ⟨ ⟨ 0, hn ⟩ ⟩ ) ( fun i => |a i| ) from by exact le_trans ( by norm_num ) ( Finset.le_sup' ( fun i => |a i| ) ( Finset.mem_univ ⟨ 0, hn ⟩ ) ) ]
