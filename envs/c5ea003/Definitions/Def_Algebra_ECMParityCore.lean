-- Prove2me | Definitions.Def_Algebra_ECMParityCore
-- name    : Algebra_ECMParityCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:13:58.067774+00:00
-- url     : https://prove2.me/theorems/0b63d1aa-4a84-4e63-8b65-83eb39b12d7f
-- title:
--   Aether Catalog definitions — Algebra_ECMParityCore
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ECMParityCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ECMParityCore.lean by skeleton subtraction
import Mathlib
/-
# ECM-PARITY, core: the parity of the point count of `y² = x³ + A x + B`

For an odd prime `p` and `A B : ZMod p` put

  `curveCard A B = 1 + #{(x,y) ∈ (ZMod p)² : y² = x³ + A x + B}`

(the `1` is the point at infinity of the projective Weierstrass model).

The main result of this file is the **parity dichotomy**

  `2 ∣ curveCard A B  ↔  the cubic x³ + A x + B has a root in ZMod p`

valid whenever the cubic is separable (`Δ = -4A³ - 27B² ≠ 0`).  Equivalently:
`#E` is odd exactly when Frobenius is a `3`-cycle on the roots of the cubic
(the cubic is irreducible over `𝔽_p`; see `ECMParityFrobenius.lean`).

The proof is elementary and self-contained:

* fibrewise counting: over each `x` the fibre `{y : y² = f x}` has odd
  cardinality iff `f x = 0`, hence `#affine ≡ #roots (mod 2)`;
* a separable cubic has `0`, `1` or `3` roots (never `2`), so `#roots` is odd
  iff `#roots ≠ 0`.

§0 collects the purely algebraic facts about a depressed cubic over an arbitrary
field (Vieta, the third root, the discriminant as a square of the root
difference product).  These are reused over the cubic extension `𝔽_{p³}` in
`ECMParityFrobenius.lean`.
-/

namespace ECMParity

open Finset

/-! ## 0. Depressed cubics over an arbitrary field -/

/-- The depressed cubic `x³ + A x + B`. -/
def cubic {R : Type*} [CommRing R] (A B x : R) : R := x ^ 3 + A * x + B

/-- The discriminant `-4A³ - 27B²` of `x³ + A x + B`. -/
def disc {R : Type*} [CommRing R] (A B : R) : R := -4 * A ^ 3 - 27 * B ^ 2

section GeneralField

variable {F : Type*} [Field F] {A B a b x : F}








end GeneralField

/-! ## 1. Fibrewise counting over `𝔽_p` -/

variable {p : ℕ} [Fact p.Prime]

/-- The set of roots of the cubic in `ZMod p`. -/
def rootSet (A B : ZMod p) : Finset (ZMod p) :=
  univ.filter (fun x => cubic A B x = 0)

/-- The affine points of `y² = x³ + A x + B`. -/
def affinePoints (A B : ZMod p) : Finset (ZMod p × ZMod p) :=
  univ.filter (fun P => P.2 ^ 2 = cubic A B P.1)

/-- The number of projective points: affine points plus the point at infinity. -/
def curveCard (A B : ZMod p) : ℕ := 1 + (affinePoints A B).card





/-! ## 2. A separable cubic has `0`, `1` or `3` roots -/




/-! ## 3. The parity dichotomy -/



end ECMParity


