-- Prove2me | Definitions.Def_Bridges_ThermodynamicJacobsonCountermodelCompression
-- name    : Bridges_ThermodynamicJacobsonCountermodelCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:50.305754+00:00
-- url     : https://prove2.me/theorems/6da3a364-da44-457e-9f7d-4c8ae7a08593
-- title:
--   Aether Catalog definitions — Bridges_ThermodynamicJacobsonCountermodelCompression
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ThermodynamicJacobsonCountermodelCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ThermodynamicJacobsonCountermodelCompression.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Thermodynamic Jacobson Reconstruction and Countermodel Compression
# for Closure-Generated Proof Semirings

This file establishes a reconstruction principle for semantics in coherent
closure-generated proof semirings with finite spectrum: the algebraic
Jacobson/nucleus semantics, the logical derivability relation, and the
thermodynamic prime semantics all collapse to a single computable object.

The compression theorem upgrades completeness into optimization: every failed
entailment admits a **canonical extremal countermodel** extracted by finite
maximization over the prime spectrum, not just an abstract existential witness.

## Main results

### Definitions
* `ThermoWitness` — a prime point with non-negative temperature parameter
* `thermoGap` — temperature-scaled evaluation gap between two elements
* `canonicalCountermodel` — the prime maximizing the separation gap

### Theorems
* `radical_entailment_iff_thermo` — Jacobson–thermodynamic coincidence:
  radical entailment equals the zero-free-energy envelope
* `not_derivable_iff_exists_extremal_prime` — finite extremal reconstruction:
  non-derivability is witnessed by a gap-maximizing prime
* `canonicalCountermodel_maximizes_gap` — the canonical countermodel achieves
  the maximum separation gap
* `canonicalCountermodel_is_countermodel_of_not_derivable` — the canonical
  countermodel has strictly positive gap when derivability fails
* `finite_spectrum_countermodel_compression` — the full compression theorem:
  non-derivability is equivalent to positivity of the canonical gap

### Helper lemmas (finite optimization)
* `exists_gap_maximizer` — existence of a maximizer over a finite nonempty type
* `positive_of_max_ge_positive` — maximizer is positive if any value is
* `no_positive_gap_iff_all_nonpositive` — negation of existence ↔ universal bound
* `thermodynamic_irrelevance_of_positive_temperature` — temperature normalization

## References

* Stone, M.H. — The theory of representations for Boolean algebras (1936)
* Lawvere, F.W. — Metric spaces, generalized logic, and closed categories (1973)
-/


noncomputable section

open Classical Finset

/-!
## § 1. Core Definitions
-/

/-- A **thermodynamic witness** packages a prime spectral point with a
non-negative temperature parameter. The temperature controls the scaling
of the separation gap; normalization to `temperature = 1` is canonical
when the only role of temperature is positive scaling. -/
structure ThermoWitness (S : Type*) [CommSemiring S] where
  /-- The prime point in the spectrum -/
  prime : PrimeSpectrum S
  /-- Temperature parameter (non-negative) -/
  temperature : ℝ
  /-- Temperature is non-negative -/
  nonneg_temperature : 0 ≤ temperature

/-- The **thermodynamic gap** (free-energy separation) between elements `x` and `y`
at a thermodynamic witness `w`. A positive gap at some witness indicates that `y`
is not entailed by `x` in the thermodynamic semantics.

  thermoGap(w, x, y) = w.temperature * (eval(w.prime, y) - eval(w.prime, x))
-/
def thermoGap
    (S : Type*) [CommSemiring S]
    (eval : PrimeSpectrum S → S → ℝ)
    (w : ThermoWitness S) (x y : S) : ℝ :=
  w.temperature * (eval w.prime y - eval w.prime x)

/-!
## § 2. Finite Optimization Lemmas

These are the technical core: pure finite-type optimization results that
do not depend on any proof-semiring structure.
-/

/-
Every real-valued function on a finite nonempty type has a maximizer.
-/
theorem exists_gap_maximizer
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    ∃ a : α, ∀ b : α, f b ≤ f a := by
  simpa using Finset.exists_max_image Finset.univ f ( Finset.univ_nonempty )

/-
If some value is positive and `a` is a maximizer, then `f a` is positive.
-/

/-
The negation of "there exists a positive value" is equivalent to
"all values are nonpositive".
-/

/-
Temperature is irrelevant for positivity of the gap when both temperatures
are strictly positive: the sign of the gap depends only on the prime point.
-/

/-!
## § 3. Canonical Countermodel Extraction

We define the canonical countermodel as the prime in the finite spectrum
that maximizes the evaluation gap `eval p y - eval p x`.
-/

variable {S : Type*} [CommSemiring S]

/-- The **canonical countermodel**: the prime in the finite spectrum that
maximizes the separation gap `eval p y - eval p x`. This is the
algorithmically extractable extremal witness for non-derivability. -/
noncomputable def canonicalCountermodel
    [Fintype (PrimeSpectrum S)] [Nonempty (PrimeSpectrum S)]
    (eval : PrimeSpectrum S → S → ℝ)
    (x y : S) : PrimeSpectrum S :=
  (exists_gap_maximizer (fun p => eval p y - eval p x)).choose

/-
The canonical countermodel achieves the maximum separation gap:
for every prime `p`, the gap at `p` is at most the gap at the
canonical countermodel.
-/

/-!
## § 4. Jacobson–Thermodynamic Coincidence

Given a Stone–prime completeness hypothesis relating derivability to the
existence of separating primes, we prove that radical entailment is exactly
the zero-free-energy envelope of the thermodynamic semantics.
-/

/-
**Radical entailment ↔ thermodynamic nonpositivity (Jacobson–thermodynamic
coincidence).**

Under a Stone–prime completeness hypothesis, radical entailment of `x` over `y`
holds if and only if no prime achieves a positive evaluation gap. This is the
conceptual center: radical closure is not merely algebraically reconstructible;
it is exactly the zero-free-energy envelope of the thermodynamic semantics.
-/

/-!
## § 5. Finite Extremal Prime Reconstruction of Non-Derivability

Every failed entailment is witnessed by a single prime maximizing the
thermodynamic separation gap. This is the finite-spectrum compression theorem.
-/

/-
**Finite extremal prime reconstruction.**

Non-derivability is equivalent to the existence of a gap-maximizing prime
with strictly positive gap. This compresses all countermodels to a single
extremal witness.
-/

/-- A **unit-temperature witness** is a `ThermoWitness` with `temperature = 1`. -/
def ThermoWitness.unitTemp {S : Type*} [CommSemiring S]
    (p : PrimeSpectrum S) : ThermoWitness S :=
  ⟨p, 1, le_of_lt one_pos⟩

/-
At unit temperature, the thermodynamic gap equals the raw evaluation gap.
-/

/-
**Finite extremal reconstruction with unit-temperature witnesses.**

Every failed entailment admits a unit-temperature `ThermoWitness` that
maximizes the raw evaluation gap among all unit-temperature witnesses
and has strictly positive gap. Temperature normalization to 1 is canonical
since the sign of the gap depends only on the prime.
-/

/-!
## § 6. Canonical Compressed Countermodel Extraction

The positive-gap extraction theorem: the canonical countermodel extracted
by finite optimization has strictly positive gap whenever derivability fails.
-/

/-
**The canonical countermodel is a countermodel when derivability fails.**

If `¬ Derivable x y`, then the canonical countermodel (the gap-maximizing prime)
has strictly positive evaluation gap. This is the algorithmic shadow of the
reconstruction theorem: proof failure can be diagnosed by a finite "most
informative" prime state.
-/

/-
**Full countermodel compression theorem.**

Non-derivability is equivalent to positivity of the canonical countermodel's
gap. This is the strongest form of the compression: a failed entailment does
not merely have some abstract countermodel; it has a canonical compressed one
extracted by finite optimization.
-/

/-!
## § 7. Axiom Verification
-/

end


