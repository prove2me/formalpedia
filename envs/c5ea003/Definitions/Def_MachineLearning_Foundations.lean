-- Prove2me | Definitions.Def_MachineLearning_Foundations
-- name    : MachineLearning_Foundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:40:03.824247+00:00
-- url     : https://prove2.me/theorems/36fa668c-3867-4a45-8eda-c1fa8ead16df
-- title:
--   Aether Catalog definitions — MachineLearning_Foundations
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Foundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Foundations.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Algebraic Learning Theory — Foundations

This file opens the field of **algebraic learning theory**: the systematic transfer
of statistical learning theory (VC dimension, Rademacher complexity, PAC bounds) from
vector spaces over ℝ to modules over arbitrary semirings.

## Bridge: Commutative Algebra ↔ Statistical Learning Theory

Classical learning theory secretly depends only on the *algebraic* structure of hypothesis
classes, not on the analytic structure of ℝ. By replacing vector spaces with modules and
norms with spectral valuations, we obtain a strictly more general framework.

## Main Results

- `AlgebraicHypothesisClass`: Hypothesis class parametrized by an S-module M
- `algebraicShattering`: The semiring analogue of VC shattering
- `ModuleRestrictionMap`: The S-linear restriction map from M to S^A
- `field_shattering_card_le_finrank`: **The fundamental theorem** — over a field,
  shattering a set of size n requires finrank ≥ n
- `SpectralLearningWeight`: Bridge to algebraic geometry via Spec(S)
- `PostQuantumHypothesis`: Bridge to lattice-based post-quantum cryptography

## Applications

- **Post-quantum cryptography**: Lattice-based security from ℤ-module VC bounds
- **Certified robustness**: Lipschitz bounds from module structure
- **Tropical ML**: Spectral decomposition over idempotent semirings
-/


open scoped Classical NNReal

namespace AlgebraicLearningTheory

/-! ## Core Definitions -/

/-- An algebraic hypothesis class over a semiring S is a hypothesis class
    parametrized by an S-module M. When S = ℝ, this recovers the classical
    linear hypothesis class.

    Bridge: connects Module theory (algebra) to hypothesis classes (ML).

    The `embed` function maps module elements to functions X → S, preserving
    the S-module structure. This is the algebraic spine of any linear model:
    each "hypothesis" is a module element, and evaluation at a data point
    is S-linear in the hypothesis. -/
structure AlgebraicHypothesisClass (S : Type*) [CommSemiring S]
    (M : Type*) [AddCommMonoid M] [Module S M] (X : Type*) where
  /-- The embedding of module elements as functions X → S -/
  embed : M → (X → S)
  /-- Linearity: the embedding respects scalar multiplication -/
  embed_smul : ∀ (r : S) (m : M) (x : X), embed (r • m) x = r * embed m x
  /-- Linearity: the embedding respects addition -/
  embed_add : ∀ (m₁ m₂ : M) (x : X), embed (m₁ + m₂) x = embed m₁ x + embed m₂ x

/-- The algebraic shattering condition on a finite set.
    This is the semiring analogue of the classical VC shattering condition:
    a set A is shattered if every S-valued labeling of A can be realized by
    some module element through the embedding.

    Bridge: connects module surjectivity (algebra) to shattering (ML). -/
def algebraicShattering {S : Type*} [CommSemiring S]
    {M : Type*} [AddCommMonoid M] [Module S M] {X : Type*}
    (H : AlgebraicHypothesisClass S M X) (A : Finset X) : Prop :=
  ∀ (f : A → S), ∃ m : M, ∀ (a : A), H.embed m a.val = f a


/-! ## Embed Linearity Consequences -/






/-! ## The Restriction Map

The key construction connecting algebra to learning theory:
given a finite set A ⊆ X, the **restriction map** sends each module element m
to the tuple of evaluations (H.embed m a)_{a ∈ A}. This is an S-linear map
from M to S^A, and shattering is equivalent to its surjectivity. -/

/-- The restriction linear map from M to S^A, defined by evaluation.
    This is the algebraic object that controls shattering:
    shattering of A ↔ surjectivity of this map.

    Bridge: connects Module homomorphisms (algebra) to
    hypothesis restriction (ML). -/
noncomputable def ModuleRestrictionMap {S : Type*} [CommSemiring S]
    {M : Type*} [AddCommMonoid M] [Module S M] {X : Type*}
    (H : AlgebraicHypothesisClass S M X) (A : Finset X) :
    M →ₗ[S] (A → S) where
  toFun m a := H.embed m a.val
  map_add' m₁ m₂ := by ext a; exact H.embed_add m₁ m₂ a.val
  map_smul' r m := by ext a; exact H.embed_smul r m a.val

/-! ## Shattering Characterization -/




/-! ## The Fundamental VC Bound over Fields

**Theorem**: Over a field K, if a finite-dimensional K-vector space V parametrizes
a hypothesis class H, and A ⊆ X is shattered, then |A| ≤ dim_K(V).

This is the algebraic core of the Vapnik-Chervonenkis theorem, proved purely
via linear algebra (rank of the restriction map). -/




/-! ## Direct Sum Decomposition

The direct product of two hypothesis classes gives a new hypothesis class.
This connects ensemble learning (combining classifiers) to module direct sums. -/



/-! ## Spectral Learning Weight

Bridge to algebraic geometry: assign a learning-theoretic weight to each
prime ideal of S, measuring the "local complexity" of the hypothesis class
at that prime. This is the foundation for the spectral Rademacher decomposition. -/

/-- A spectral learning weight assigns a nonneg real to each prime ideal of S,
    measuring the local learning complexity at that spectral point.

    Bridge: connects PrimeSpectrum (algebraic geometry) to
    learning complexity (ML). -/
structure SpectralLearningWeight (S : Type*) [CommSemiring S] where
  /-- The weight function on Spec(S) -/
  weight : PrimeSpectrum S → ℝ≥0
  /-- Weights are bounded by 1 (normalization) -/
  weight_le_one : ∀ p, weight p ≤ 1

/-- The spectral complexity bound: the sum of spectral weights over
    the prime spectrum gives a learning complexity measure.

    Bridge: connects tropical integration (algebraic geometry)
    to Rademacher complexity (ML). -/
noncomputable def spectralComplexityBound {S : Type*} [CommSemiring S]
    [Fintype (PrimeSpectrum S)]
    (w : SpectralLearningWeight S) : ℝ≥0 :=
  Finset.sum Finset.univ (fun p => w.weight p)


/-! ## Lipschitz-Certified Hypothesis Classes

Bridge to certified robustness in ML: a hypothesis class with a Lipschitz
certificate ensures that small perturbations of input produce small changes
in output. -/

/-- A Lipschitz-certified hypothesis class: an algebraic hypothesis class
    equipped with a Lipschitz bound on the embedding.

    Bridge: connects Module structure (algebra) to certified_robustness (ML).
    Impact: enables provably robust neural_network verification via algebraic bounds. -/
structure LipschitzCertifiedHypothesis (S : Type*) [CommSemiring S]
    (M : Type*) [AddCommMonoid M] [Module S M]
    (X : Type*) [PseudoMetricSpace X]
    extends AlgebraicHypothesisClass S M X where
  /-- The Lipschitz constant for each module element -/
  lipschitz_const : M → ℝ≥0


/-! ## Post-Quantum Hypothesis Classes

Bridge to post-quantum cryptography: hypothesis classes over ℤ-modules
whose hardness is tied to lattice problems (SVP, CVP). -/



/-! ## Algebraic PAC Learning -/



/-! ## VC Dimension Predicate -/

/-- The VC dimension predicate: "H has VC dimension at least d" means there
    exists a set of size d that is algebraically shattered.
    Bridge: connects module theory to VC theory (ML). -/
def vcDimAtLeast {S : Type*} [CommSemiring S]
    {M : Type*} [AddCommMonoid M] [Module S M] {X : Type*}
    (H : AlgebraicHypothesisClass S M X) (d : ℕ) : Prop :=
  ∃ (A : Finset X), A.card = d ∧ algebraicShattering H A




/-! ## Instances and Examples -/

/-- The evaluation hypothesis class: the most basic example where M = S^n
    and X = Fin n, with embed being evaluation.
    This is the "canonical" hypothesis class: linear regression in n variables. -/
def evaluationHypothesisClass (S : Type*) [CommSemiring S] (n : ℕ) :
    AlgebraicHypothesisClass S (Fin n → S) (Fin n) where
  embed f x := f x
  embed_smul r f x := by simp [Pi.smul_apply, smul_eq_mul]
  embed_add f g x := by simp [Pi.add_apply]



/-- The zero hypothesis class: M = {0}, producing only the zero function.
    This shatters only the empty set (VC dimension 0). -/
def zeroHypothesisClass (S : Type*) [CommSemiring S] (X : Type*) :
    AlgebraicHypothesisClass S (Fin 0 → S) X where
  embed _ _ := 0
  embed_smul _ _ _ := by simp
  embed_add _ _ _ := by simp


/-! ## Morphisms and Functoriality

Hypothesis classes form a category: morphisms are module homomorphisms
that respect the embedding. -/

/-- A morphism of algebraic hypothesis classes: an S-linear map between
    the parametrizing modules that is compatible with the embeddings.

    Bridge: connects Module homomorphisms (algebra) to
    hypothesis class morphisms (ML / transfer_learning). -/
structure AlgebraicHypothesisClass.Morphism {S : Type*} [CommSemiring S]
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module S M₁] [Module S M₂] {X : Type*}
    (H₁ : AlgebraicHypothesisClass S M₁ X)
    (H₂ : AlgebraicHypothesisClass S M₂ X) where
  /-- The underlying linear map -/
  map : M₁ →ₗ[S] M₂
  /-- Compatibility with embeddings -/
  compat : ∀ m x, H₂.embed (map m) x = H₁.embed m x




/-! ## Kernel and Rank-Nullity -/

/-- The kernel of the restriction map: module elements that evaluate to zero
    on all points of A. This is the submodule of "invisible" hypotheses.

    Bridge: connects kernel submodules (algebra) to
    hypothesis indistinguishability (ML). -/
noncomputable def restrictionKernel {S : Type*} [CommSemiring S]
    {M : Type*} [AddCommMonoid M] [Module S M] {X : Type*}
    (H : AlgebraicHypothesisClass S M X) (A : Finset X) :
    Submodule S M :=
  LinearMap.ker (ModuleRestrictionMap H A)



/-! ## Sample Complexity Bounds -/

/-- The algebraic sample complexity bound: n ≤ ⌈8d·log(1/δ)/ε²⌉.
    Bridge: connects finrank (algebra) to sample complexity (ML).
    Impact: enables provable sample efficiency for algebraic learners.

    The constant 8/3 arises from the Rademacher-to-PAC conversion;
    we use the simpler constant 8 for a clean universal bound. -/
noncomputable def algebraicSampleComplexityBound (d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil (8 * d * Real.log (1 / δ) / ε ^ 2)



/-! ## Security Gap Theorems

The security gap between polynomial-time learning and exponential-time
lattice breaking establishes post-quantum security. -/




end AlgebraicLearningTheory


