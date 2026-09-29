-- Prove2me | solution 1 for Bridges.AlgebraEMLLogic.primeIndicator_isClosureValuation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:19.603145+00:00
-- url     : https://prove2.me/submissions/3dcf4e01-df3b-4e34-999b-1ddca398e313

-- Sol generated from Bridges/ClosureStoneSpectrumDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureStoneSpectrumDuality
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

open Bridges.AlgebraEMLLogic

/-! ## §1. Closure Operator Axiomatics -/


variable {α : Type*}




/-! ## §2. Basic Closure Lemmas -/






/-! ## §3. Lattice of Closed Theories -/







/-! ## §4. Spectral Completeness Theorem -/

/-
**Spectral Completeness**: φ ∈ C(Γ) iff every prime closed theory
containing Γ also contains φ. Forward: monotonicity. Backward: prime separation.
-/

/-
Every closed theory is the intersection of prime closed theories over it.
-/

/-! ## §5. Certified Reconstruction -/


/-
The reconstructed operator is always a closure operator.
-/


/-! ## §6. Indicator Valuations -/


/-
Two distinct closed theories are separated by a prime indicator.
-/

/-
Every prime indicator respects closure equivalence.
-/

/-! ## §7. Join-Irreducible Closed Theories -/



/-! ## §8. Generator Rank = Join-Irreducible Count -/


/-! ## §9. Finite Closure Spectrum Structure -/







open Bridges.AlgebraEMLLogic in
theorem solution    {C : Set α → Set α} (hC : IsClosureOp C) (P : Set α) (hP : IsPrimeClosed C P) :
    ∀ x y, (x ∈ C {y} ∧ y ∈ C {x}) → primeIndicator P x = primeIndicator P y := by
  intro x y hxy
  have hxy_closure : x ∈ P ↔ y ∈ P := by
    constructor <;> intro h;
    · have h_closure : C {x} ⊆ P := by
        have h_closure : C {x} ⊆ C P := by
          exact hC.mono ( Set.singleton_subset_iff.mpr h );
        exact h_closure.trans ( hP.is_closed.symm ▸ Set.Subset.refl _ );
      exact h_closure hxy.2;
    · have h_closure : C {y} ⊆ C P := by
        exact hC.mono ( Set.singleton_subset_iff.mpr h );
      exact hP.is_closed.symm ▸ h_closure hxy.1;
  unfold primeIndicator; aesop;
