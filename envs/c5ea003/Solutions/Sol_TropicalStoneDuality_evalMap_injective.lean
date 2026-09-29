-- Prove2me | solution 1 for TropicalStoneDuality.evalMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:44.42707+00:00
-- url     : https://prove2.me/submissions/dc57abc9-f111-4ef2-bb3d-6b22cb7b654a

-- Sol generated from Bridges/TropicalPrimeStoneDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalPrimeStoneDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Prime–Stone Duality via Congruence Spectra

## Overview

We formalize a Stone-type reconstruction theorem for idempotent commutative semirings
through the lens of congruence spectra. The central result: under a spectral separation
axiom, the canonical evaluation map from a semiring into the product of its prime-congruence
quotients is an injective semiring homomorphism, yielding a faithful spectral representation.

This bridges:
- **Stone duality** (classical: Boolean algebras ↔ Stone spaces) to the semiring setting
- **Tropical geometry** (prime congruences replace prime ideals in idempotent algebra)
- **Cryptographic hardness** (spectral separation certificates → inversion lower bounds)

## Main Definitions

* `PrimeCong S` — a proper (nontrivial) ring congruence on `S`
* `SpecC S` — the congruence spectrum (type of prime congruences)
* `basicOpen a b` — the basic open set of congruences separating `a` from `b`
* `SpectrallySeparated S` — the spectral separation axiom
* `evalComponent` — projection to a single quotient (a ring homomorphism)
* `evalMap` — the full evaluation map into the product of all quotients

## Main Results

* `evalComponent_eq_iff` — evaluation equality characterizes congruence
* `evalMap_injective` — spectral separation implies injectivity of the evaluation map
* `stone_reconstruction` — the evaluation map is an injective ring homomorphism
* `evalMap_injective_iff_separated` — complete characterization of injectivity
* `basicOpen_empty_iff` — basic opens are empty iff elements are universally congruent
* `basicOpen_symm` — basic opens are symmetric in their arguments
* `separated_of_evalMap_injective` — converse: injectivity implies separation
* `quotient_idem_add` — idempotency propagates to quotients
* `evalMap_preserves_idem` — the evaluation map preserves idempotency
-/

noncomputable section

open Function Set

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open TropicalStoneDuality

/-! ## Section 1: Idempotent Semirings and Prime Congruences -/






/-! ## Section 2: Basic Open Set Properties -/






/-! ## Section 3: The Evaluation Map and Stone Reconstruction -/



/-- Two elements have the same image under `evalComponent p` iff they are `p`-congruent. -/
theorem evalComponent_eq_iff {S : Type*} [NonAssocSemiring S] (p : SpecC S) (a b : S) :
    evalComponent p a = evalComponent p b ↔ p.rel a b :=
  RingCon.eq p.rel






/-! ## Section 4: The Evaluation Map as a Ring Homomorphism -/








/-! ## Section 5: Idempotent Structure Propagation -/



/-! ## Section 6: Basic Opens Form a Separation System -/



/-! ## Section 7: Observer Family Connection

We show how `PrimeCong` connects to `FiniteProofObserverFamily` from the catalog. -/




open TropicalStoneDuality in
theorem solution{S : Type*} [NonAssocSemiring S]
    (hsep : SpectrallySeparated S) : Injective (evalMap S) := by
  intro a b hab
  by_contra hne
  obtain ⟨p, hp⟩ := hsep a b hne
  have heq : evalMap S a p = evalMap S b p := congr_fun hab p
  simp only [evalMap, evalComponent_eq_iff] at heq
  exact hp heq
