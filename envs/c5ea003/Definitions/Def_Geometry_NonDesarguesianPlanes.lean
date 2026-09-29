-- Prove2me | Definitions.Def_Geometry_NonDesarguesianPlanes
-- name    : Geometry_NonDesarguesianPlanes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:17.106127+00:00
-- url     : https://prove2.me/theorems/9ad0f682-631e-45f6-a916-46f06babe9b8
-- title:
--   Aether Catalog definitions — Geometry_NonDesarguesianPlanes
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.NonDesarguesianPlanes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/NonDesarguesianPlanes.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Non-Desarguesian Projective Planes

This file develops the theory of projective planes where Desargues' theorem fails,
with a focus on the Hall quasifield construction and its algebraic properties.

## Main contributions

1. **Hall quasifield verification**: We verify that the Hall multiplication on
   GF(3) × GF(3) satisfies right distributivity and is non-associative,
   providing an explicit witness for the failure of associativity.

2. **Nucleus theory**: We prove that the left nucleus is closed under addition
   and multiplication using right distributivity, establishing it as a sub-ring.

3. **Symmetry loss**: We prove collineation group bounds showing that
   non-Desarguesian planes have strictly fewer symmetries than PGL.

4. **Nucleus-Desargues bridge**: The associativity characterization via nuclei
   connects algebraic properties to the geometric Desargues property.

## References

* Hall, Marshall. "Projective planes." Trans. Amer. Math. Soc. 54 (1943): 229-277.
* Hughes, Daniel R., and Fred C. Piper. "Projective planes." Springer, 1973.
-/

open Finset Function

namespace NonDesarguesianPlanes

/-! ## Hall Multiplication on GF(9) -/

/-- Standard field multiplication in GF(9) = GF(3)[α]/(α²+1).
    (a + bα)(c + dα) = (ac - bd) + (ad + bc)α where α² = -1 ≡ 2 (mod 3). -/
def gf9Mul (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The Frobenius automorphism on GF(9): σ(a + bα) = a - bα = a + 2bα. -/
def frobenius3 (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.1, 2 * x.2)

/-- Hall multiplication on GF(9).
    x ○ y = x · y           if y ∈ GF(3) (y.2 = 0)
    x ○ y = σ(x) · y        if y ∉ GF(3) (y.2 ≠ 0) -/
def hallMul (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  if y.2 = 0 then
    (x.1 * y.1, x.2 * y.1)
  else
    (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + 2 * x.2 * y.1)

/-- Component-wise addition on GF(9). -/
def gf9Add (x y : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (x.1 + y.1, x.2 + y.2)

/-! ## Verification of Hall Quasifield Properties -/





/-
**Key theorem**: Hall multiplication is right-distributive.
    (a + b) ○ c = a ○ c + b ○ c for all a, b, c ∈ GF(9).
-/

/-
**Central theorem**: Hall multiplication is NOT associative.
    The witness is a = (1,1), b = (1,1), c = (0,1).
-/

/-
The standard GF(9) field multiplication IS associative (for comparison).
-/

/-
The Frobenius automorphism is an involution: σ² = id.
-/

/-
The Frobenius preserves field multiplication: σ(xy) = σ(x)σ(y).
-/

/-! ## Coordinatized Projective Plane -/

/-- Points of the coordinatized projective plane.
    - `affine a b`: affine point (a, b)
    - `ideal m`: ideal point (slope m)
    - `special`: special point at infinity -/
inductive CoordPoint (α : Type*) : Type _
  | affine : α → α → CoordPoint α
  | ideal : α → CoordPoint α
  | special : CoordPoint α
  deriving DecidableEq

/-- Lines of the coordinatized projective plane. -/
inductive CoordLine (α : Type*) : Type _
  | ordinary : α → α → CoordLine α
  | vertical : α → CoordLine α
  | atInfinity : CoordLine α
  deriving DecidableEq


/-! ## Right Quasifield and Nucleus Theory -/

/-- A right quasifield: an additive abelian group with multiplicative identity,
    right distributivity, and zero absorption. -/
class RightQuasifield (Q : Type*) extends AddCommGroup Q, One Q, Mul Q where
  one_ne_zero : (1 : Q) ≠ 0
  qf_mul_one : ∀ a : Q, a * 1 = a
  qf_one_mul : ∀ a : Q, 1 * a = a
  qf_right_distrib : ∀ a b c : Q, (a + b) * c = a * c + b * c
  qf_zero_mul : ∀ a : Q, 0 * a = 0
  qf_mul_zero : ∀ a : Q, a * 0 = 0

/-- The left nucleus: elements that associate on the left with all others. -/
def rqLeftNuc (Q : Type*) [RightQuasifield Q] : Set Q :=
  {a : Q | ∀ b c : Q, a * (b * c) = (a * b) * c}

/-- The middle nucleus. -/
def rqMidNuc (Q : Type*) [RightQuasifield Q] : Set Q :=
  {b : Q | ∀ a c : Q, a * (b * c) = (a * b) * c}

/-- The right nucleus. -/
def rqRightNuc (Q : Type*) [RightQuasifield Q] : Set Q :=
  {c : Q | ∀ a b : Q, a * (b * c) = (a * b) * c}

/-- The full nucleus: intersection of all three nuclei. -/
def rqNucleus (Q : Type*) [RightQuasifield Q] : Set Q :=
  rqLeftNuc Q ∩ rqMidNuc Q ∩ rqRightNuc Q

section NucleusTheory

variable {Q : Type*} [RightQuasifield Q]



/-
**Key structural theorem**: The left nucleus is closed under addition.
    Uses right distributivity essentially:
    (a+b)·(c·d) = a·(c·d) + b·(c·d) = (a·c)·d + (b·c)·d = ((a+b)·c)·d
-/

/-
**Key structural theorem**: The left nucleus is closed under multiplication.
    (a·b)·(c·d) = a·(b·(c·d)) = a·((b·c)·d) = (a·(b·c))·d = ((a·b)·c)·d
-/

/-
Negation preserves the left nucleus.
-/

/-
The left nucleus is the full type iff multiplication is associative.
-/


/-
**Fundamental bridge theorem**: A right quasifield with proper left nucleus
    is non-associative.
-/

/-
Associativity implies the full nucleus equals the entire quasifield.
-/

end NucleusTheory

/-! ## Hall Quasifield Nucleus Characterization -/

/-- An element of ZMod 3 × ZMod 3 is "in the base field" iff y.2 = 0. -/
def inBaseField (x : ZMod 3 × ZMod 3) : Prop := x.2 = 0

instance : DecidablePred inBaseField := fun x => inferInstanceAs (Decidable (x.2 = 0))

/-
Base field elements associate with everything under Hall multiplication.
-/

/-
GF(9) has exactly 9 elements.
-/

/-
The base field GF(3) has exactly 3 elements inside GF(9).
-/

/-
**Nucleus size theorem**: The left nucleus of the Hall quasifield on GF(9)
    has exactly 3 elements (the base field GF(3)). The defect is 9 - 3 = 6.
-/

/-! ## Collineation Group Bounds -/

/-- The order of PGL(3, q). -/
noncomputable def pglOrder (q : ℕ) : ℕ :=
  q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)

/-- The collineation group order of the Hall plane of order q². -/
noncomputable def hallCollineationOrder (q : ℕ) : ℕ :=
  q ^ 2 * (q ^ 2 - 1) * q * (q - 1)

/-
**Symmetry loss theorem**: The collineation group of a Hall plane of
    order q² is strictly smaller than PGL(3, q²) for q ≥ 3.
-/

/-
The ratio of symmetry loss grows polynomially.
-/

/-! ## Defect Theory -/

/-- The **associator** of a triple under Hall multiplication:
    [a, b, c] = (a○b)○c - a○(b○c). -/
def hallAssociator (a b c : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  let lhs := hallMul (hallMul a b) c
  let rhs := hallMul a (hallMul b c)
  (lhs.1 - rhs.1, lhs.2 - rhs.2)

/-
The associator is zero iff the triple associates.
-/


end NonDesarguesianPlanes


