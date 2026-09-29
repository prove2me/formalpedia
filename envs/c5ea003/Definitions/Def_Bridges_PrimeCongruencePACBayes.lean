-- Prove2me | Definitions.Def_Bridges_PrimeCongruencePACBayes
-- name    : Bridges_PrimeCongruencePACBayes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:11.707087+00:00
-- url     : https://prove2.me/theorems/f257f1d9-1f5a-4f8a-aea2-8cbfea2c5beb
-- title:
--   Aether Catalog definitions — Bridges_PrimeCongruencePACBayes
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PrimeCongruencePACBayes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PrimeCongruencePACBayes.lean by skeleton subtraction
import Mathlib

/-!
# Prime-Congruence PAC–Bayes Duality via Spectral Separation

This file formalizes a bridge theory that turns prime-congruence semantics into
a statistical learning principle. The core insight: **generalization can be recast
as spectral separability** — posterior complexity equals the energy required to
separate hypotheses on a prime-congruence observer space.

## Main Results

### Structures and Definitions
* `PrimeCongruenceSpectrumPoint` — prime-like observer congruence on a hypothesis space
* `SpectralSeparator` — weighted observer that distinguishes hypotheses
* `SeparatesPosterior` — predicate: a separator distinguishes posterior from complement
* `posteriorSpectralComplexity` — infimum weight of separating observers
* `CompressionCertificate` — finite certificate witnessing separation
* `IsFiniteSpectralCover` — finite family covering all posterior/complement distinctions

### Theorems
* `genGap_le_posteriorSpectralComplexity` — generalization gap ≤ spectral complexity
* `posteriorSpectralComplexity_le_genGap` — reverse inequality via ε-approximation
* `posteriorSpectralComplexity_eq_genGap` — exact duality (equality)
* `exists_canonicalCompressionCertificate` — finite cover → compression certificate
* `exists_cardinality_bounded_certificate` — certificate with cardinality bound

## Bridge

Connects prime congruence spectra (algebra) → PAC–Bayes learning theory (ML) →
sample compression (information theory) → Stone duality (logic) →
tropical geometry (min-plus optimization).
-/

set_option maxHeartbeats 800000

open Set

/-! ## I. Spectrum and Separator Structures -/

/-- A point of the prime-congruence spectrum: an equivalence relation on hypotheses
    with a prime-like separation property. -/
structure PrimeCongruenceSpectrumPoint (A : Type*) where
  rel : A → A → Prop
  is_equiv : Equivalence rel
  prime_like : ∃ x y : A, ¬ rel x y

/-- A spectral separator: a weighted observer that distinguishes hypotheses. -/
structure SpectralSeparator (A : Type*) where
  point : PrimeCongruenceSpectrumPoint A
  weight : ENNReal
  separates : A → A → Prop

/-- A separator separates a posterior class Q from its complement. -/
def SeparatesPosterior {A : Type*} (sep : SpectralSeparator A) (Q : Set A) : Prop :=
  ∀ ⦃h h' : A⦄, h ∈ Q → h' ∉ Q → sep.separates h h'

/-- The posterior spectral complexity: the infimum weight over all separating observers. -/
noncomputable def posteriorSpectralComplexity {A : Type*}
    (Obs : Set (SpectralSeparator A)) (Q : Set A) : ENNReal :=
  sInf {w | ∃ sep ∈ Obs, SeparatesPosterior sep Q ∧ sep.weight = w}

/-- A compression certificate: a finite witness of posterior separation. -/
structure CompressionCertificate (A : Type*) where
  support : Finset A
  budget : ENNReal
  certifies : Set A → Prop

/-- A finite spectral cover: a finite family of separators that collectively
    distinguish all posterior elements from all complement elements. -/
def IsFiniteSpectralCover {A : Type*}
    (C : Finset (SpectralSeparator A)) (Q : Set A) : Prop :=
  ∀ ⦃h h' : A⦄, h ∈ Q → h' ∉ Q → ∃ sep ∈ C, sep.separates h h'

/-! ## II. Core Duality Theorems -/

/-
**Spectral PAC–Bayes Duality (Upper Bound).**
    If the generalization gap is bounded by every separating observer's weight,
    then it is bounded by the posterior spectral complexity.
-/

/-
**Spectral PAC–Bayes Duality (Lower Bound).**
    If for every ε > 0 there exists a separating observer of weight ≤ genGap Q + ε,
    then the posterior spectral complexity is ≤ genGap Q.
-/


/-! ## III. Compression Certificate Theorems -/

/-
**Canonical Compression Certificate from Finite Spectral Cover.**
-/

/-
**Cardinality-Bounded Certificate.**
-/

/-! ## IV. Structural Properties -/

/-
A single separating observer gives an upper bound on spectral complexity.
-/

/-
If Q = univ (the full type), then every element is in Q, so there are no
    complement elements, and SeparatesPosterior is vacuously true for all separators.
    Hence spectral complexity equals the infimum of all observer weights.
-/

/-
The empty posterior has spectral complexity equal to the infimum of all
    observer weights, since SeparatesPosterior is vacuously true for ∅.
-/

/-
If some observer has zero weight, the empty posterior has zero complexity.
-/

/-
Adding more observers can only decrease complexity (antitone in observers).
-/


