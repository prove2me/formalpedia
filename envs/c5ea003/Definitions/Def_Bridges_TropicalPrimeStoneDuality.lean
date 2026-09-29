-- Prove2me | Definitions.Def_Bridges_TropicalPrimeStoneDuality
-- name    : Bridges_TropicalPrimeStoneDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:51.019345+00:00
-- url     : https://prove2.me/theorems/a2812d77-f993-4729-ad3d-64cf3336ca24
-- title:
--   Aether Catalog definitions — Bridges_TropicalPrimeStoneDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalPrimeStoneDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalPrimeStoneDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalStoneDuality

/-! ## Section 1: Idempotent Semirings and Prime Congruences -/

/-- An idempotent commutative semiring: `a + a = a` for all `a`.
This is the algebraic axiom distinguishing tropical semirings from classical ones.
In the min-plus semiring (ℝ, min, +), idempotency of min is the defining property. -/
class IdempotentAddCommSemiring (S : Type*) extends CommSemiring S where
  idem_add : ∀ a : S, a + a = a

/-- A **prime congruence** on a semiring `S`: a ring congruence that is proper
(does not identify all elements). This is the semiring analogue of a prime ideal
in ring theory — the building block of the congruence spectrum.

In tropical geometry, prime congruences replace prime ideals because
idempotent semirings lack additive inverses, making ideal theory inadequate. -/
structure PrimeCong (S : Type*) [Add S] [Mul S] where
  /-- The underlying ring congruence -/
  rel : RingCon S
  /-- The congruence is proper: it does not identify all elements -/
  proper : ∃ a b : S, ¬ rel a b

/-- The **congruence spectrum** of `S`: the type of all prime congruences.
This is the tropical analogue of `Spec R` in algebraic geometry. -/
def SpecC (S : Type*) [Add S] [Mul S] := PrimeCong S

/-- The **basic open set** `D(a,b)` in the congruence spectrum:
the set of prime congruences that distinguish `a` from `b`.

This is the semiring analogue of the Zariski basic open `D(f)` in scheme theory. -/
def basicOpen {S : Type*} [Add S] [Mul S] (a b : S) : Set (SpecC S) :=
  {p | ¬ p.rel a b}

/-- The **spectral separation axiom**: for any two distinct elements of `S`,
there exists a prime congruence distinguishing them.

This is the semiring-congruence analogue of the T₀ separation axiom in topology. -/
def SpectrallySeparated (S : Type*) [Add S] [Mul S] : Prop :=
  ∀ a b : S, a ≠ b → ∃ p : SpecC S, ¬ p.rel a b

/-! ## Section 2: Basic Open Set Properties -/






/-! ## Section 3: The Evaluation Map and Stone Reconstruction -/

/-- The **evaluation component** at a prime congruence `p`:
the canonical ring homomorphism `S →+* S/p`. -/
def evalComponent {S : Type*} [NonAssocSemiring S] (p : SpecC S) : S →+* p.rel.Quotient :=
  RingCon.mk' p.rel



/-- The **full evaluation map**: sends `a : S` to the tuple of its equivalence classes
across all prime congruences. This is the map `η_S : S → Π p : SpecC S, S/p`.

This is the semiring-level analogue of the Gelfand transform or Stone representation. -/
def evalMap (S : Type*) [NonAssocSemiring S] : S → (∀ p : SpecC S, p.rel.Quotient) :=
  fun a p => evalComponent p a





/-! ## Section 4: The Evaluation Map as a Ring Homomorphism -/

/-- The evaluation map preserves addition. -/
theorem evalMap_add {S : Type*} [NonAssocSemiring S] (a b : S) :
    evalMap S (a + b) = evalMap S a + evalMap S b := by
  ext p; simp [evalMap, evalComponent, map_add]

/-- The evaluation map preserves multiplication. -/
theorem evalMap_mul {S : Type*} [NonAssocSemiring S] (a b : S) :
    evalMap S (a * b) = evalMap S a * evalMap S b := by
  ext p; simp [evalMap, evalComponent, map_mul]

/-- The evaluation map sends 0 to 0. -/
theorem evalMap_zero {S : Type*} [NonAssocSemiring S] :
    evalMap S 0 = 0 := by
  ext p; simp [evalMap, evalComponent, map_zero]

/-- The evaluation map sends 1 to 1. -/
theorem evalMap_one {S : Type*} [NonAssocSemiring S] :
    evalMap S 1 = 1 := by
  ext p; simp [evalMap, evalComponent, map_one]

/-- **The evaluation map as a ring homomorphism.**

Combined with injectivity, this gives the full Stone reconstruction:
`S` is isomorphic (via `η`) to its image in the product of quotients. -/
def evalRingHom (S : Type*) [NonAssocSemiring S] :
    S →+* (∀ p : SpecC S, p.rel.Quotient) where
  toFun := evalMap S
  map_zero' := evalMap_zero
  map_one' := evalMap_one
  map_add' := evalMap_add
  map_mul' := evalMap_mul



/-! ## Section 5: Idempotent Structure Propagation -/



/-! ## Section 6: Basic Opens Form a Separation System -/



/-! ## Section 7: Observer Family Connection

We show how `PrimeCong` connects to `FiniteProofObserverFamily` from the catalog. -/

/-- Convert a finite family of prime congruences into an observer family. -/
def primeFamilyToObservers {S : Type*} [Add S] [Mul S]
    (n : ℕ) (ps : Fin n → PrimeCong S) :
    { F : Fin n → RingCon S // ∀ i, ∃ a b : S, ¬ (F i) a b } :=
  ⟨fun i => (ps i).rel, fun i => (ps i).proper⟩


end TropicalStoneDuality


