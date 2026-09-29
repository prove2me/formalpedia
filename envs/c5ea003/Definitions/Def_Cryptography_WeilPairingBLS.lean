-- Prove2me | Definitions.Def_Cryptography_WeilPairingBLS
-- name    : Cryptography_WeilPairingBLS
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:03:05.889909+00:00
-- url     : https://prove2.me/theorems/37b9b8ec-c264-4388-9099-ef42a2a5ef57
-- title:
--   Aether Catalog definitions — Cryptography_WeilPairingBLS
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.WeilPairingBLS`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/WeilPairingBLS.lean by skeleton subtraction
import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Finset.Card

/-!
# Weil pairings and the algebraic security core of BLS signatures

This development uses Mathlib's nonsingular affine points of a `WeierstrassCurve`.
A `WeilPairing` is the standard algebraic interface on the `n`-torsion subgroup:
bilinearity, alternation, image torsion, and nondegeneracy.  The BLS result is the
algebraic EUF-CMA-to-CDH reduction under the explicit fresh-message random-oracle
programming event.  Aggregate correctness and constant group-element size are also proved.
-/

open scoped BigOperators
open Finset

namespace Cryptography.WeilBLS

universe u v

variable {F : Type u} [Field F] [DecidableEq F]

/-- The existing Mathlib elliptic-curve point group for an affine Weierstrass curve. -/
abbrev CurvePoint (W : WeierstrassCurve F) := W.toAffine.Point

/-- The `n`-torsion subgroup of the Mathlib elliptic-curve point group. -/
def torsionPoints (W : WeierstrassCurve F) (n : ℕ) : AddSubgroup (CurvePoint W) where
  carrier := {P | n • P = 0}
  zero_mem' := nsmul_zero n
  add_mem' := by
    intro P Q hP hQ
    change n • (P + Q) = 0
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' := by
    intro P hP
    change n • (-P) = 0
    rw [smul_neg, hP, neg_zero]

/-- A Weil pairing on elliptic-curve `n`-torsion.  `Additive μ` lets the two additive
homomorphisms encode a multiplicative pairing without reintroducing bilinearity axioms. -/
structure WeilPairing (W : WeierstrassCurve F) (n : ℕ) (μ : Type v) [CommGroup μ] where
  hom : torsionPoints W n →+ torsionPoints W n →+ Additive μ
  alternating : ∀ P : torsionPoints W n, hom P P = 0
  image_torsion : ∀ P Q : torsionPoints W n, (Additive.toMul (hom P Q)) ^ n = 1
  nondegenerate_left : ∀ P : torsionPoints W n,
    (∀ Q : torsionPoints W n, hom P Q = 0) → P = 0
  nondegenerate_right : ∀ Q : torsionPoints W n,
    (∀ P : torsionPoints W n, hom P Q = 0) → Q = 0

namespace WeilPairing

variable {W : WeierstrassCurve F} {n : ℕ} {μ : Type v} [CommGroup μ]
    (e : WeilPairing W n μ)

/-- Multiplicative notation for the pairing. -/
def pair (P Q : torsionPoints W n) : μ := Additive.toMul (e.hom P Q)










end WeilPairing

/-! ## BLS signatures and CDH reduction -/

section BLS

variable {W : WeierstrassCurve F} {n : ℕ} {μ : Type v} [CommGroup μ]

/-- Public BLS parameters over elliptic-curve torsion. -/
structure BLSParams (W : WeierstrassCurve F) (n : ℕ) (μ : Type v) [CommGroup μ] where
  pairing : WeilPairing W n μ
  generator : torsionPoints W n
  pairing_generator_injective : Function.Injective (fun P => pairing.pair P generator)

namespace BLSParams

variable (P : BLSParams W n μ)

/-- Public-key generation from a natural scalar. -/
def publicKey (sk : ℕ) : torsionPoints W n := sk • P.generator

/-- BLS signing in the hash-to-curve abstraction. -/
def sign (_P : BLSParams W n μ) (sk : ℕ) (hashPoint : torsionPoints W n) :
    torsionPoints W n := sk • hashPoint

/-- Pairing-based BLS verification. -/
def verifies (pk hashPoint signature : torsionPoints W n) : Prop :=
  P.pairing.pair signature P.generator = P.pairing.pair hashPoint pk



/-- A computational Diffie--Hellman challenge in additive notation. -/
structure CDHChallenge (P : BLSParams W n μ) where
  publicA : torsionPoints W n
  publicB : torsionPoints W n
  secretA : ℕ
  publicA_eq : publicA = P.publicKey secretA

/-- The CDH target. -/
def CDHChallenge.target (C : CDHChallenge P) : torsionPoints W n :=
  C.secretA • C.publicB

/-- The standard BLS reduction's fresh-message oracle-programming event. -/
structure ProgrammedFreshChallenge (P : BLSParams W n μ) (Message : Type*)
    [DecidableEq Message] where
  challenge : CDHChallenge P
  hashToCurve : Message → torsionPoints W n
  targetMessage : Message
  queriedMessages : Finset Message
  fresh : targetMessage ∉ queriedMessages
  programmed : hashToCurve targetMessage = challenge.publicB


/-- CDH hardness against a specified class of attainable outputs.  This formulation keeps
the computational assumption explicit instead of pretending that it is an algebraic fact. -/
def CDHHardFor (C : CDHChallenge P) (attainable : torsionPoints W n → Prop) : Prop :=
  ¬ attainable C.target


/-- Aggregate a finite family of signatures by elliptic-curve addition. -/
def aggregate {ι : Type*} (s : Finset ι) (signature : ι → torsionPoints W n) :
    torsionPoints W n := ∑ i ∈ s, signature i




end BLSParams
end BLS

end Cryptography.WeilBLS


