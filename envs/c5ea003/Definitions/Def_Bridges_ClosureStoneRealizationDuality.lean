-- Prove2me | Definitions.Def_Bridges_ClosureStoneRealizationDuality
-- name    : Bridges_ClosureStoneRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:25:48.838169+00:00
-- url     : https://prove2.me/theorems/61aa7fde-0e43-477a-8d2a-f03179cd67f9
-- title:
--   Aether Catalog definitions — Bridges_ClosureStoneRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureStoneRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureStoneRealizationDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# Closure–Stone Realization Duality via Idempotent Consequence Semimodules

This file establishes a finite duality/reconstruction theorem at the
Algebra–EML–Logic interface, bridging:
- finite logical consequence data (closure operators),
- canonical algebraic objects (implicational bases),
- Stone/Priestley-style spectral semantics (prime closed theories).

## Main Results

* `closed_inter` — intersection of closed sets is closed
* `closed_sInter` — arbitrary intersection of closed sets is closed
* `cl_closed` — `cl A` is always closed
* `closure_from_basis_is_closure_operator` — closure from implications is a closure operator
* `exists_finite_implicational_basis` — every finite closure operator has a finite basis
* `closure_table_recovers_basis_and_spectrum` — the main reconstruction theorem
* `closure_iso_preserves_structure` — functorial invariance under isomorphism

## Mathematical Overview

Given a finite type `X` and a closure operator `cl : Set X → Set X`, we construct:
1. The lattice of closed sets (closed under arbitrary intersection)
2. A finite implicational basis that reconstructs `cl` exactly
3. The space of meet-prime closed theories as a finite spectral space
4. A proof that this data is invariant under closure-table isomorphism

This establishes a certified bridge: closure table ≃ canonical basis ≃ prime spectrum.
-/

open Set Finset

namespace ClosureStoneDuality

variable {X : Type*}

/-! ## Part 1: Closure Operators -/

/-- A closure operator on sets: extensive, monotone, idempotent. -/
structure IsClosureOperator (cl : Set X → Set X) : Prop where
  extensive : ∀ A, A ⊆ cl A
  monotone : ∀ ⦃A B : Set X⦄, A ⊆ B → cl A ⊆ cl B
  idempotent : ∀ A, cl (cl A) = cl A

/-- A set is closed under `cl` if `cl A = A`. -/
def IsClosed (cl : Set X → Set X) (A : Set X) : Prop := cl A = A

/-
The intersection of two closed sets is closed.
-/

/-
The intersection of any family of closed sets is closed.
-/

/-
`cl A` is always a closed set.
-/

/-
If A is closed and A ⊇ B, then A ⊇ cl B.
-/

/-
The universe is always closed.
-/


/-! ## Part 2: Implications and Bases -/

/-- An implication `premise → conclusion` on a finite type. -/
structure Implication (X : Type*) where
  premise : Finset X
  conclusion : X

instance [DecidableEq X] : DecidableEq (Implication X) := by
  intro a b
  cases a; cases b
  simp only [Implication.mk.injEq]
  exact inferInstance

/-- A set satisfies an implication if: premise ⊆ A implies conclusion ∈ A. -/
def SatisfiesImplication (A : Set X) (r : Implication X) : Prop :=
  (↑r.premise : Set X) ⊆ A → r.conclusion ∈ A

/-- A set satisfies all implications in a collection. -/
def SatisfiesAll (A : Set X) (B : Set (Implication X)) : Prop :=
  ∀ r ∈ B, SatisfiesImplication A r

/-- Closure from a basis: the intersection of all supersets of A that satisfy all implications. -/
def ClosureFromBasis (B : Set (Implication X)) (A : Set X) : Set X :=
  ⋂₀ {S : Set X | A ⊆ S ∧ SatisfiesAll S B}

/-
The universe satisfies all implications.
-/

/-
ClosureFromBasis is extensive.
-/

/-
ClosureFromBasis is monotone.
-/

/-
ClosureFromBasis result satisfies all implications.
-/

/-
ClosureFromBasis is idempotent.
-/


/-! ## Part 3: Sound and Complete Bases -/

/-- An implication is sound for `cl` if `cl` respects it. -/
def IsSound (cl : Set X → Set X) (r : Implication X) : Prop :=
  ∀ A, (↑r.premise : Set X) ⊆ cl A → r.conclusion ∈ cl A

/-- A basis is sound for `cl` if every implication in it is sound. -/
def BasisSound (cl : Set X → Set X) (B : Set (Implication X)) : Prop :=
  ∀ r ∈ B, IsSound cl r

/-- A basis is complete for `cl` if its closure equals `cl`. -/
def BasisComplete (cl : Set X → Set X) (B : Set (Implication X)) : Prop :=
  ∀ A, ClosureFromBasis B A = cl A

/-- A basis reconstructs `cl` if it is both sound and complete. -/
def ReconstructsClosure (cl : Set X → Set X) (B : Set (Implication X)) : Prop :=
  BasisSound cl B ∧ BasisComplete cl B

/-
Soundness: if B is sound for cl, then cl A ⊆ implies ClosureFromBasis B A ⊆ cl A
    for any A, since cl A satisfies all sound implications.
-/

/-! ## Part 4: Full Basis Construction -/

/-- The full implicational basis: all implications (S, x) where x ∈ cl(↑S). -/
def FullBasis [Fintype X] [DecidableEq X] (cl : Set X → Set X) : Set (Implication X) :=
  {r : Implication X | r.conclusion ∈ cl (↑r.premise : Set X)}

/-
The full basis is sound.
-/

/-
Any set closed under all full-basis implications is cl-closed.
    Key lemma for completeness.
-/

/-
The full basis is complete: ClosureFromBasis (FullBasis cl) = cl.
-/


/-! ## Part 5: Meet-Prime Closed Theories and Spectral Structure -/

/-- A closed set P is meet-prime if whenever A ∩ B ⊆ P for closed A, B,
    then A ⊆ P or B ⊆ P. -/
def IsMeetPrimeClosed (cl : Set X → Set X) (P : Set X) : Prop :=
  IsClosed cl P ∧ P ≠ Set.univ ∧
  ∀ ⦃A B : Set X⦄, IsClosed cl A → IsClosed cl B →
    A ∩ B ⊆ P → A ⊆ P ∨ B ⊆ P

/-- Prime separability: distinct closed sets are separated by meet-prime closed theories. -/
def PrimeSeparable (cl : Set X → Set X) : Prop :=
  ∀ ⦃A B : Set X⦄, cl A ≠ cl B →
    ∃ P, IsMeetPrimeClosed cl P ∧
      ((cl A ⊆ P ∧ ¬cl B ⊆ P) ∨ (cl B ⊆ P ∧ ¬cl A ⊆ P))

/-- The prime spectrum of a closure operator. -/
def PrimeSpectrum (cl : Set X → Set X) : Set (Set X) :=
  {P | IsMeetPrimeClosed cl P}



/-! ## Part 6: Closure Table Isomorphism -/

variable {Y : Type*}

/-- An isomorphism of closure tables: a bijection on elements that commutes
    with the closure operators. -/
structure ClosureTableIso [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (clX : Set X → Set X) (clY : Set Y → Set Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  commutes : ∀ A : Set X, Set.image toFun (clX A) = clY (Set.image toFun A)

variable {Y : Type*}

/-
A closure table isomorphism maps closed sets to closed sets.
-/

/-
A closure table isomorphism preserves meet-primality.
-/

/-! ## Part 7: Main Reconstruction Theorems -/


/-
**Theorem B: Prime Spectrum Structure.**
    Under prime separability, the prime spectrum faithfully separates
    the closed sets, establishing the spectral half of the duality.
-/



end ClosureStoneDuality


