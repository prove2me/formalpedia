-- Prove2me | Definitions.Def_Bridges_ClosureStoneSpectrumDuality
-- name    : Bridges_ClosureStoneSpectrumDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:53.505912+00:00
-- url     : https://prove2.me/theorems/e3a4dff6-a7cc-485b-bd2a-04d5989964b0
-- title:
--   Aether Catalog definitions — Bridges_ClosureStoneSpectrumDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureStoneSpectrumDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureStoneSpectrumDuality.lean by skeleton subtraction
import Mathlib
/-
# Finite Closure–Stone Spectrum Duality via Idempotent Theory Semimodules

This file formalizes a finite duality theorem at the interface of algebra, logic,
and spectral semantics. The core result is that a finite closure system can be
canonically recovered from its spectrum of prime closed theories.

## Main Results

* `IsClosureOp` — Closure operator axioms (extensive, monotone, idempotent)
* `IsPrimeClosed` — Prime closed theory definition
* `mem_closure_iff_prime_forall` — Spectral completeness theorem
* `closed_eq_sInter_primes_over` — Closed = intersection of primes over it
* `reconstructClosure_eq` — Certified reconstruction of closure from spectrum
* `reconstructClosure_isClosureOp` — Reconstruction yields a closure operator
* `primeIndicator_separates` — Prime indicators separate closed theories
* `primeIndicator_isClosureValuation` — Prime indicators respect closure equiv
* `genRank_eq_card_joinIrreducibles` — Generator rank = join-irreducible count

## Bridges

- **Closure Logic ↔ Spectral Topology**: Closure operators ↔ finite Stone spectra
- **Algebra ↔ Logic**: Semimodule generators ↔ join-irreducible closed theories
- **Semantics ↔ Reconstruction**: Spectrum and closure functors are mutually inverse
-/


set_option maxHeartbeats 800000

open Set Function Classical

noncomputable section

namespace Bridges.AlgebraEMLLogic

/-! ## §1. Closure Operator Axiomatics -/

/-- A closure operator on `Set α`: extensive, monotone, idempotent. -/
structure IsClosureOp {α : Type*} (C : Set α → Set α) : Prop where
  extensive : ∀ s, s ⊆ C s
  mono : Monotone C
  idempotent : ∀ s, C (C s) = C s

variable {α : Type*}

/-- A set is closed if it equals its own closure. -/
def IsClosed (C : Set α → Set α) (T : Set α) : Prop := C T = T

/-- A closed theory `P` is meet-prime if whenever the intersection of two
closed theories is contained in `P`, one of them must be contained in `P`. -/
structure IsPrimeClosed (C : Set α → Set α) (P : Set α) : Prop where
  is_closed : IsClosed C P
  prime_meet : ∀ ⦃A B : Set α⦄, IsClosed C A → IsClosed C B →
    A ∩ B ⊆ P → A ⊆ P ∨ B ⊆ P

/-- Prime separation: for any closed theory T and element φ ∉ T, there
exists a prime closed theory containing T but not φ. -/
def PrimeSeparation (C : Set α → Set α) : Prop :=
  ∀ (T : Set α), IsClosed C T → ∀ φ, φ ∉ T →
    ∃ P, IsPrimeClosed C P ∧ T ⊆ P ∧ φ ∉ P

/-! ## §2. Basic Closure Lemmas -/






/-! ## §3. Lattice of Closed Theories -/



/-- The join of two closed theories is the closure of their union. -/
def closedSup (C : Set α → Set α) (A B : Set α) : Set α := C (A ∪ B)




/-! ## §4. Spectral Completeness Theorem -/

/-
**Spectral Completeness**: φ ∈ C(Γ) iff every prime closed theory
containing Γ also contains φ. Forward: monotonicity. Backward: prime separation.
-/

/-
Every closed theory is the intersection of prime closed theories over it.
-/

/-! ## §5. Certified Reconstruction -/

/-- Reconstruct a closure operator from prime theories:
C(Γ) = {φ | ∀ P prime, Γ ⊆ P → φ ∈ P}. -/
def reconstructClosure (primes : Set (Set α)) : Set α → Set α :=
  fun Γ => {φ | ∀ P ∈ primes, Γ ⊆ P → φ ∈ P}

/-
The reconstructed operator is always a closure operator.
-/
theorem reconstructClosure_isClosureOp (primes : Set (Set α)) :
    IsClosureOp (reconstructClosure primes) := by
  constructor;
  · exact fun s x hx P hP hP' => hP' hx;
  · exact fun s t hst φ hφ => fun P hP hP' => hφ P hP ( hst.trans hP' );
  · intro s;
    ext x;
    grind +locals


/-! ## §6. Indicator Valuations -/

/-- The indicator valuation of a prime closed theory P:
maps φ to `true` if φ ∉ P, `false` if φ ∈ P. -/
def primeIndicator (P : Set α) : α → Bool :=
  fun φ => decide (φ ∉ P)

/-
Two distinct closed theories are separated by a prime indicator.
-/

/-
Every prime indicator respects closure equivalence.
-/

/-! ## §7. Join-Irreducible Closed Theories -/



/-! ## §8. Generator Rank = Join-Irreducible Count -/


/-! ## §9. Finite Closure Spectrum Structure -/

/-- A finite closure spectrum bundles prime theories with basic opens. -/
structure FinClosureSpectrum (α : Type*) where
  C : Set α → Set α
  primes : Set (Set α)
  all_prime : ∀ P ∈ primes, IsPrimeClosed C P
  basicOpen : α → Set (Set α)
  basicOpen_def : ∀ φ, basicOpen φ = {P ∈ primes | φ ∉ P}

/-- Construct the spectrum from a closure operator. -/
def spectrumOf (C : Set α → Set α) : FinClosureSpectrum α where
  C := C
  primes := {P | IsPrimeClosed C P}
  all_prime := fun _ hP => hP
  basicOpen φ := {P | IsPrimeClosed C P ∧ φ ∉ P}
  basicOpen_def φ := by
    ext P; simp only [mem_setOf_eq]

/-- Minimal closure presentation recovered from a spectrum. -/
structure MinClosurePresentation (α : Type*) where
  closure : Set α → Set α
  is_closure_op : IsClosureOp closure
  reconstruction_source : Set (Set α)

/-- Reconstruct a closure presentation from a spectrum. -/
def reconstructPresentation (X : FinClosureSpectrum α) : MinClosurePresentation α where
  closure := reconstructClosure X.primes
  is_closure_op := reconstructClosure_isClosureOp X.primes
  reconstruction_source := X.primes


end Bridges.AlgebraEMLLogic


