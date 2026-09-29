-- Prove2me | Definitions.Def_Bridges_TropicalOneWayMinors
-- name    : Bridges_TropicalOneWayMinors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:46.858995+00:00
-- url     : https://prove2.me/theorems/f5128a2a-d05a-4726-8ea8-60659b3f781e
-- title:
--   Aether Catalog definitions — Bridges_TropicalOneWayMinors
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalOneWayMinors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalOneWayMinors.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical One-Way Minors via Valuation Congruence Obstructions
# and Certified Collision Separation

## Bridge: Tropical Algebra ↔ Cryptographic Hardness Certificates

This file establishes a formal bridge between **tropical algebraic invariants**
and **certified cryptographic collision separation**. The central result shows
that separation of valuation-congruence profiles — built from principal tropical
minors, kernel data, and semiring congruence classes — is equivalent to
collision-freeness for finitely generated tropical semigroup actions on a
bounded input ball, with constructive extraction of bounded obstruction witnesses
when collisions do occur.

## Main Results

* `tropicalAct_nil`, `tropicalAct_cons` — action semantics
* `evalWordMatrix_nil`, `evalWordMatrix_append` — word evaluation functoriality
* `tropicalAct_eq_evalWordMatrix_mulVec` — action = matrix-vector product
* `tropical_minor_congruence_collision_bridge` — the main bridge theorem:
    profile separation + witness soundness ⟹ collision-freeness
* `collision_iff_bounded_congruence_obstruction` — biconditional bridge
* `no_collision_on_ball_of_no_bounded_witness` — no witness ⟹ no collision
* `extract_witness_of_collision_on_ball` — collision ⟹ bounded witness
* `collision_free_on_ball_of_profile_separation` — profile sep ⟹ no collision
* `verifier_sound` — algorithmic verifier correctness
* `collision_separation_radius_mono` — separation monotonicity in radius
* `collision_free_length_one` — collision-freeness for length-1 words

## Cross-domain Bridges

- **Tropical geometry ↔ Cryptography**: Principal tropical minors as geometric
  fingerprints; separation of minors as tropical distance amplification.
- **Semiring congruence theory ↔ Hardness certificates**: Congruence obstructions
  as formal certificates of non-collapse.
- **Automata/Nerode theory ↔ Collision resistance**: Collision-free action on a
  finite radius ball as a bounded distinguishability theorem.
- **Valuation theory ↔ Proof-carrying cryptography**: Computable valuation profiles
  with formalized witness extraction.
-/


namespace TropicalOneWayMinors

open Matrix Finset BigOperators

/-! ## Section 1: Core Definitions

We define tropical matrix action on vectors, word evaluation, and the
abstract profile/witness framework for collision separation. -/

variable {Gen : Type*} {S : Type*} {n : ℕ}

/-- Evaluate a word (list of generators) as a matrix product.
    Each generator maps to a matrix; the word evaluates to their product.
    This is the semigroup homomorphism from the free monoid on `Gen`
    to the matrix monoid `Matrix (Fin n) (Fin n) S`. -/
def evalWordMatrix [Semiring S] (M : Gen → Matrix (Fin n) (Fin n) S) :
    List Gen → Matrix (Fin n) (Fin n) S
  | [] => 1
  | g :: w => M g * evalWordMatrix M w




/-- The tropical action of a word on a vector: multiply the word's matrix by the vector.
    This models the semigroup action of the tropical matrix semigroup on vectors. -/
def tropicalAct [Semiring S] (M : Gen → Matrix (Fin n) (Fin n) S)
    (v₀ : Fin n → S) (w : List Gen) : Fin n → S :=
  evalWordMatrix M w *ᵥ v₀





/-! ## Section 2: Valuation-Congruence Profile

An abstract profile type bundling:
- principal tropical minors of the evaluated matrix,
- a bounded kernel witness class,
- a semiring congruence certificate class. -/

/-- A valuation-congruence profile for an `n×n` matrix over `S`.
    Bundles principal minors, kernel rank data, and congruence class.
    This is the tropical algebraic analogue of a cryptographic fingerprint. -/
structure ValCongProfile (n : ℕ) (S : Type*) where
  /-- Principal minor values (diagonal entries of the matrix). -/
  principalMinors : Fin n → S
  /-- Kernel obstruction datum (bounded rank information). -/
  kernelDatum : ℕ
  /-- Congruence certificate class identifier. -/
  congClass : ℕ
  deriving DecidableEq

/-- Construct a basic profile from a matrix by extracting diagonal entries. -/
def basicProfile [Semiring S] [DecidableEq S]
    (A : Matrix (Fin n) (Fin n) S) : ValCongProfile n S where
  principalMinors := fun i => A i i
  kernelDatum := 0
  congClass := 0

/-- The profile associated to a word via its evaluated matrix. -/
def wordProfile [Semiring S] [DecidableEq S]
    (M : Gen → Matrix (Fin n) (Fin n) S) (w : List Gen) : ValCongProfile n S :=
  basicProfile (evalWordMatrix M w)

/-! ## Section 3: The Collision Ball -/


/-- The action is collision-free on the ball of radius R if no two distinct
    words of length ≤ R produce the same output. -/
def collisionFreeOnBall [Semiring S] (M : Gen → Matrix (Fin n) (Fin n) S)
    (v₀ : Fin n → S) (R : ℕ) : Prop :=
  ∀ ⦃w₁ w₂ : List Gen⦄,
    w₁.length ≤ R → w₂.length ≤ R →
    tropicalAct M v₀ w₁ = tropicalAct M v₀ w₂ → w₁ = w₂

/-! ## Section 4: Main Bridge Theorems -/

/-
**Main Bridge Theorem (Forward Direction).**
Profile separation combined with witness soundness implies that
equal profiles force distinct actions.

This is the cryptographic heart: if valuation-congruence profiles are
well-separated (no bounded witness can explain profile equality) and
collisions always produce bounded witnesses, then equal profiles guarantee
distinct outputs.

**Proof strategy**: By contrapositive. Suppose `tropicalAct M v₀ w₁ = tropicalAct M v₀ w₂`.
Then `hcollision` produces a bounded witness. But `hseparated` says equal profiles
admit no bounded witness. Contradiction.
-/

/-
**Biconditional Bridge Theorem.**
Collision on the ball is equivalent to the existence of a bounded
congruence obstruction witness.
-/

/-
**No-Collision Corollary.**
If no bounded witness exists for any pair of distinct words on the ball,
then the action is collision-free.
-/

/-
**Witness Extraction Corollary.**
Any collision on the ball yields an explicit bounded witness.
This is the constructive direction: collisions are algebraically explainable.
-/

/-
**Collision-freeness from profile separation.**
If the profile map is injective on the ball, and collisions force profile
equality, then the action is collision-free.
-/

/-! ## Section 5: Algorithmic Verifier -/

/-
**Verifier Soundness.**
If a verifier certifies separation, then the action is collision-free
on words with matching profiles.
-/

/-! ## Section 6: Structural Properties -/

/-
**Witness monotonicity and radius transfer.**
If collision separation holds at radius R₂, it holds for words within R₁ ≤ R₂.
-/

/-
**Profile separation excludes collision.**
If collisions produce witnesses and no witness exists, no collision occurs.
-/

/-
**Collision implies profile collapse or witness (dichotomy).**
Any collision on the ball is explained either by profile equality or by
a bounded witness. This is a direct consequence of the dichotomy hypothesis.
-/

/-
**No collision when profile-separated and witness-free.**
If collisions must produce either profile equality or a witness, and we have
neither equal profiles nor any witness, then no collision can occur.
-/

/-! ## Section 7: Concrete Instantiation -/



/-! ## Section 8: Semigroup Action Properties -/



/-
For a word of length 1, collision-freeness reduces to matrix injectivity
    on the input vector.
-/


end TropicalOneWayMinors


