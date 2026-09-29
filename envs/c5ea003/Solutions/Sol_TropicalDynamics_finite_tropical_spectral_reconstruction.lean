-- Prove2me | solution 1 for TropicalDynamics.finite_tropical_spectral_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:05:01.460508+00:00
-- url     : https://prove2.me/submissions/beb0b7bd-5f67-4ec7-af94-0419fe3e07c8

-- Sol generated from Bridges/TropicalSpectralDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalSpectralDuality
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


open TropicalDynamics

variable {S : Type*} [IdemSemiring S]
variable {M : Type*} [AddCommMonoid M] [Module S M]

/-! ## Core Definitions -/










/-! ## Observable Equivalence is a Setoid -/





/-! ## Observation Map Properties -/

/-- The observation map intertwines T with coordinatewise scaling when all functionals
    are eigenfunctionals. This is the core spectral intertwining theorem. -/
theorem obs_map_intertwines {n : ℕ} (T : M →ₗ[S] M)
    (E : Fin n → M →ₗ[S] S) (ev : Fin n → S)
    (hE : ∀ i, IsEigenfunctional T (E i) (ev i)) :
    ConjugateScaling T E ev := by
  intro x
  ext i
  exact hE i x



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


open TropicalDynamics in
theorem solution    (T : M →ₗ[S] M) (Q : Setoid M)
    (hsep : ∃ (n : ℕ) (E : Fin n → M →ₗ[S] S) (ev : Fin n → S),
      (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q) :
    ∃ (n : ℕ) (E : Fin n → M →ₗ[S] S) (ev : Fin n → S),
      (∀ i, IsEigenfunctional T (E i) (ev i)) ∧
      SeparatesIdx E Q ∧
      ConjugateScaling T E ev ∧
      IsObserverDimension T Q n := by
  -- By definition of `IsObserverDimension`, there exists a minimal finite eigenfamily that separates Q.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, IsObserverDimension T Q n := by
    obtain ⟨n, h⟩ : ∃ n, ∃ (E : Fin n → M →ₗ[S] S) (ev : Fin n → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q := by
      exact hsep;
    obtain ⟨E, ev, hE, hsep⟩ := h;
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≤ n ∧ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q ∧ ∀ m' < m, ¬∃ (E' : Fin m' → M →ₗ[S] S) (ev' : Fin m' → S), (∀ i, IsEigenfunctional T (E' i) (ev' i)) ∧ SeparatesIdx E' Q := by
      have h_observer_dimension : ∃ m : ℕ, m ≤ n ∧ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q := by
        exact ⟨ n, le_rfl, E, ev, hE, hsep ⟩;
      obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≤ n ∧ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q ∧ ∀ m' < m, ¬∃ (E' : Fin m' → M →ₗ[S] S) (ev' : Fin m' → S), (∀ i, IsEigenfunctional T (E' i) (ev' i)) ∧ SeparatesIdx E' Q := by
        have h_min : ∃ m ∈ {m | m ≤ n ∧ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q}, ∀ m' ∈ {m | m ≤ n ∧ ∃ (E : Fin m → M →ₗ[S] S) (ev : Fin m → S), (∀ i, IsEigenfunctional T (E i) (ev i)) ∧ SeparatesIdx E Q}, m ≤ m' := by
          apply_rules [ Set.exists_min_image ];
          exact Set.finite_iff_bddAbove.mpr ⟨ n, fun m hm => hm.1 ⟩
        obtain ⟨ m, hm₁, hm₂ ⟩ := h_min;
        exact ⟨ m, hm₁.1, hm₁.2.choose, hm₁.2.choose_spec.choose, hm₁.2.choose_spec.choose_spec.1, hm₁.2.choose_spec.choose_spec.2, fun m' hm' hm'' => not_lt_of_ge ( hm₂ m' ⟨ le_trans hm'.le hm₁.1, hm'' ⟩ ) hm' ⟩;
      exact ⟨ m, hm ⟩;
    exact ⟨ m, ⟨ hm.2.choose, hm.2.choose_spec.choose, hm.2.choose_spec.choose_spec.1, hm.2.choose_spec.choose_spec.2.1 ⟩, fun m' hm' => hm.2.choose_spec.choose_spec.2.2 m' hm' ⟩;
  use n;
  rcases hn.1 with ⟨ E, ev, hE, hsep ⟩ ; exact ⟨ E, ev, hE, hsep, obs_map_intertwines T E ev hE, hn ⟩ ;
