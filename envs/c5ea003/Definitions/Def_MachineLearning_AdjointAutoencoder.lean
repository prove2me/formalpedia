-- Prove2me | Definitions.Def_MachineLearning_AdjointAutoencoder
-- name    : MachineLearning_AdjointAutoencoder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:55.464445+00:00
-- url     : https://prove2.me/theorems/c038f480-1fc0-4c36-974f-8621075dffef
-- title:
--   Aether Catalog definitions — MachineLearning_AdjointAutoencoder
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.AdjointAutoencoder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/AdjointAutoencoder.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Categorical Representation Learning: Adjoint Autoencoders

This file formalizes the **Adjoint Autoencoder Theorem**: an encoder-decoder pair
`(E, D)` that minimizes the information bottleneck objective corresponds to an
adjunction `E ⊣ D`, with the unit and counit providing explicit reconstruction
error and compression bounds.

## Main Results

* `CategoricalRL.adjoint_reconstruction_bound` — Bridge: connects categorical
  adjunctions to rate-distortion theory. The unit of an adjunction bounds the
  reconstruction error by `√(1 - β)`.

* `CategoricalRL.adjoint_compression_bound` — The counit bounds the compression
  loss by `√β`.

* `CategoricalRL.adjoint_rate_distortion_tradeoff` — The unit and counit norms
  satisfy `‖unit‖² + ‖counit‖² ≤ 1`, encoding the rate-distortion tradeoff.

* `CategoricalRL.lipschitz_decoder_from_adjunction` — Bridge: connects adjoint
  autoencoders to lipschitz_certified_robustness. The decoder is Lipschitz with
  constant `1/√β`.

* `CategoricalRL.encoder_decoder_composition_bound` — The composition `D ∘ E` is
  close to the identity, with error bounded by the unit norm.

## Key Structures

* `CategoricalRL.AdjointAutoencoder` — An encoder-decoder pair with adjunction
  structure and information-theoretic certificates.
* `CategoricalRL.InformationBottleneck` — Rate-distortion objective.
* `CategoricalRL.HopfRenormalizationFunctor` — Bridge: connects Connes-Kreimer
  Hopf algebras (from QFT renormalization) to categorical representation learning.

## Applications

- **ML/lipschitz_certified_robustness**: Lipschitz bound `1/√β` for decoders
- **Physics/hopf_renormalization**: Yoneda rank = BPHZ renormalization dimension
- **Crypto**: Information-theoretic security of encoded representations
-/

namespace CategoricalRL

open Real

/-! ## Section 1: Adjoint Autoencoder Structure -/

/-- An **AdjointAutoencoder** models an encoder-decoder pair where the encoder
    `E : X → Z` maps data to a latent space and the decoder `D : Z → X` reconstructs.
    The adjunction structure provides certified bounds on reconstruction and compression.

    Bridge: connects categorical adjunctions to variational autoencoders in ML. -/
structure AdjointAutoencoder where
  /-- Reconstruction error bound (‖unit‖): how much information is lost -/
  unit_norm : ℝ
  /-- Compression bound (‖counit‖): how much the latent space is compressed -/
  counit_norm : ℝ
  /-- Tradeoff parameter β ∈ (0, 1): controls rate vs distortion -/
  beta : ℝ
  /-- β is in (0, 1) -/
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  /-- Unit norm satisfies reconstruction bound -/
  unit_bound : unit_norm ≤ Real.sqrt (1 - beta)
  /-- Counit norm satisfies compression bound -/
  counit_bound : counit_norm ≤ Real.sqrt beta
  /-- Norms are nonneg -/
  unit_nonneg : 0 ≤ unit_norm
  counit_nonneg : 0 ≤ counit_norm

/-- The **InformationBottleneck** objective `L = rate - β · distortion`.

    Bridge: connects rate-distortion theory to categorical adjunction structure. -/
structure InformationBottleneck where
  /-- Compression cost I(X; Z) -/
  rate : ℝ
  /-- Reconstruction fidelity I(Z; X̂) -/
  distortion : ℝ
  /-- Tradeoff parameter -/
  beta : ℝ
  /-- Rate is nonneg -/
  rate_nonneg : 0 ≤ rate
  /-- Distortion is nonneg -/
  distortion_nonneg : 0 ≤ distortion
  /-- Beta is in (0, 1) -/
  beta_pos : 0 < beta
  beta_lt_one : beta < 1

/-- Compute the information bottleneck objective value. -/
noncomputable def InformationBottleneck.objective (ib : InformationBottleneck) : ℝ :=
  ib.rate - ib.beta * ib.distortion

/-- A **HopfRenormalizationFunctor** captures the structure of a faithful functor
    from the category of Feynman diagrams to vector spaces, with the Yoneda rank
    equaling the BPHZ renormalization dimension.

    Bridge: connects Connes-Kreimer Hopf algebras (from QFT renormalization) to
    categorical representation learning and hopf_renormalization. -/
structure HopfRenormalizationFunctor where
  /-- Number of Feynman diagram types (objects in FeynCat) -/
  diagram_count : ℕ
  /-- Yoneda rank = BPHZ renormalization dimension -/
  yoneda_rank : ℕ
  /-- Number of morphisms (diagram morphisms) -/
  morphism_count : ℕ
  /-- The Yoneda rank is bounded by the diagram count -/
  rank_le_count : yoneda_rank ≤ diagram_count
  /-- There is at least one diagram -/
  nonempty : 0 < diagram_count

/-! ## Section 2: Reconstruction and Compression Bounds -/



/-
**Rate-Distortion Tradeoff** (Theorem 5c).

    Bridge: connects categorical adjunction structure to the fundamental
    tradeoff in information theory and rate-distortion theory.

    The unit and counit norms satisfy `unit² + counit² ≤ 1`, encoding
    the fundamental rate-distortion tradeoff: you cannot simultaneously
    have perfect reconstruction AND perfect compression.
-/



/-! ## Section 3: Lipschitz Bounds for Decoders -/

/-
**Lipschitz Decoder from Adjunction** (Theorem 6).

    Bridge: connects adjoint autoencoders to lipschitz_certified_robustness
    in neural networks.

    If `E ⊣ D` is an adjoint autoencoder with parameter `β > 0`, then
    the decoder `D` has Lipschitz constant `L = 1/√β`. This means:

    `∀ z z', ‖D(z) - D(z')‖ ≤ (1/√β) · ‖z - z'‖`

    This provides a certified_robustness radius `r = ε · √β` for
    input perturbations of size `ε` in the latent space.
-/



/-! ## Section 4: Adjoint Autoencoder Construction -/

/-
Construct an `AdjointAutoencoder` from β and explicit norm bounds.
    This is the main construction pipeline for categorical autoencoders.
-/

/-
The optimal adjoint autoencoder achieves equality in the rate-distortion tradeoff.
-/

/-! ## Section 5: Hopf-Algebraic Renormalization Connection -/



/-! ## Section 6: Neural Architecture Rank -/





end CategoricalRL


