-- Prove2me | Definitions.Def_Bridges_TropicalSpectralDuality
-- name    : Bridges_TropicalSpectralDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:12.711421+00:00
-- url     : https://prove2.me/theorems/0279c411-5dce-4a50-9a66-bc120b75064b
-- title:
--   Aether Catalog definitions — Bridges_TropicalSpectralDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSpectralDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSpectralDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Spectral Duality via Idempotent Koopman Semimodules

This file develops a spectral semantics for idempotent discrete dynamics.
We show that for finitely generated, order-preserving, tropical-linear systems,
finite observability and finite spectrality coincide.

## Main definitions

* `TropicalDynamics.IsEigenfunctional` — a linear functional φ satisfying φ(T x) = ev * φ(x)
* `TropicalDynamics.ObsEquiv` — observable equivalence: x ~ y iff all eigenfunctionals agree
* `TropicalDynamics.ObsMap` — the observation map M → (Fin n → S)
* `TropicalDynamics.Separates` — a family separates points modulo a setoid
* `TropicalDynamics.ConjugateScaling` — observation map intertwines T with diagonal scaling

## Main results

* `obs_equiv_setoid` — observable equivalence is a setoid
* `obs_map_intertwines` — eigenfunctionals turn T into coordinatewise scaling
* `separating_family_injective_on_quotient` — separation ⟹ injective quotient embedding
* `finite_minimal_separating_subfamily` — any finite separating family has a minimal subfamily
* `tropical_observer_dimension_unique` — the observer dimension is unique
* `finite_tropical_spectral_reconstruction` — main reconstruction theorem
-/


namespace TropicalDynamics

variable {S : Type*} [IdemSemiring S]
variable {M : Type*} [AddCommMonoid M] [Module S M]

/-! ## Core Definitions -/

/-- A linear functional `φ : M →ₗ[S] S` is an eigenfunctional for `T` with eigenvalue `ev`
    if `φ (T x) = ev * φ x` for all `x`. This is the tropical analogue of a Koopman
    eigenfunction. -/
def IsEigenfunctional (T : M →ₗ[S] M) (φ : M →ₗ[S] S) (ev : S) : Prop :=
  ∀ x : M, φ (T x) = ev * φ x

/-- Observable equivalence: two states are equivalent if every functional in a family
    assigns them the same value. This is the tropical analogue of the Myhill-Nerode relation. -/
def ObsEquiv (E : Set (M →ₗ[S] S)) (x y : M) : Prop :=
  ∀ φ ∈ E, φ x = φ y

/-- A finite family of functionals separates a setoid if distinct equivalence classes
    are distinguished by some functional in the family. -/
def SeparatesSetoid (E : Finset (M →ₗ[S] S)) (Q : Setoid M) : Prop :=
  ∀ ⦃x y : M⦄, ¬ Q.r x y → ∃ φ ∈ E, φ x ≠ φ y

/-- The observation map sends a state to its tuple of functional values. -/
def ObsMap {n : ℕ} (E : Fin n → M →ₗ[S] S) : M → (Fin n → S) :=
  fun x i => E i x

/-- The observation map intertwines T with coordinatewise scaling by eigenvalues. -/
def ConjugateScaling {n : ℕ} (T : M →ₗ[S] M) (E : Fin n → M →ₗ[S] S)
    (ev : Fin n → S) : Prop :=
  ∀ x : M, ObsMap E (T x) = fun i => ev i * ObsMap E x i

/-- The observable equivalence induced by a finite indexed family. -/
def ObsEquivFin {n : ℕ} (E : Fin n → M →ₗ[S] S) (x y : M) : Prop :=
  ∀ i : Fin n, E i x = E i y

/-- A family separates a setoid (indexed version). -/
def SeparatesIdx {n : ℕ} (E : Fin n → M →ₗ[S] S) (Q : Setoid M) : Prop :=
  ∀ ⦃x y : M⦄, ¬ Q.r x y → ∃ i : Fin n, E i x ≠ E i y


/-- The observer dimension: the minimal size of a separating eigenfamily. -/
def IsObserverDimension (T : M →ₗ[S] M) (Q : Setoid M) (n : ℕ) : Prop :=
  (∃ (E : Fin n → M →ₗ[S] S) (ev : Fin n → S),
    (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q) ∧
  (∀ m < n, ¬ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S),
    (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q)

/-! ## Observable Equivalence is a Setoid -/





/-! ## Observation Map Properties -/




/-! ## Eigenfunctional Stability -/



/-! ## Quotient Dynamics -/


/-! ## Orbit Iterated Scaling -/

/-
Iterating T gives scaling by the iterated eigenvalues.
-/

/-
The forward orbit values under the observation map satisfy a tropical recurrence.
-/

/-! ## Observable Quotient Refinement -/

/-
Adding more functionals can only refine the observable equivalence.
-/

/-! ## Finite Minimal Separating Subfamily -/

/-
If a Finset of functionals separates a setoid, then a minimal separating
    subset exists (by finiteness of the Finset).
-/

/-! ## Observer Dimension Uniqueness -/

/-
If two observer dimensions exist, they must be equal.
-/

/-! ## Idempotent/Closure Operator Specialization -/

/-
For an idempotent operator (T ∘ T = T), eigenfunctionals with eigenvalue 1
    are exactly the T-invariant functionals.
-/

/-! ## Main Reconstruction Theorem -/

/-
**Finite Tropical Spectral Reconstruction (Conditional Form)**

Given:
- An idempotent semiring S and an S-module M
- An S-linear endomorphism T
- A setoid Q on M (the "observable quotient")
- A hypothesis that Q is separated by finitely many eigenfunctionals

Then there exists a finite eigenfamily that:
1. Separates Q (gives an injective quotient embedding into Sⁿ)
2. Conjugates T to coordinatewise scaling
3. Has minimal cardinality (the observer dimension)
-/

end TropicalDynamics


