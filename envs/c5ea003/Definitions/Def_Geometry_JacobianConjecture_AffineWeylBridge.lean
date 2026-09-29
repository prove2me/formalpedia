-- Prove2me | Definitions.Def_Geometry_JacobianConjecture_AffineWeylBridge
-- name    : Geometry_JacobianConjecture_AffineWeylBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:17.314908+00:00
-- url     : https://prove2.me/theorems/db8ddc87-4a58-400a-bed8-1d56dd2c520f
-- title:
--   Aether Catalog definitions — Geometry_JacobianConjecture_AffineWeylBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.JacobianConjecture.AffineWeylBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/JacobianConjecture/AffineWeylBridge.lean by skeleton subtraction
import Mathlib

/-!
# An affine Jacobian–Weyl algebra bridge

The Jacobian and Dixmier conjectures are linked by a classical passage between
commutative polynomial maps and endomorphisms of Weyl algebras.  This file proves
a fully explicit degree-one instance of that connection.

For an affine polynomial map

`F(X,Y) = (aX + bY + c, dX + eY + f)`,

the commutative Jacobian determinant is `a*e - b*d`.  In every (possibly
noncommutative) rational algebra, replacing `X,Y` by elements `x,y` gives

`[F₁(x,y), F₀(x,y)] = (a*e - b*d) • [y,x]`.

Consequently, Jacobian determinant one transports the Weyl relation `[y,x]=1`.
This is a precise bridge from commutative algebraic geometry to noncommutative
ring theory: the same determinant controls preservation of both area and the
canonical Weyl commutator.
-/

open MvPolynomial

namespace JacobianConjecture.AffineWeylBridge

/-- The additive commutator `[x,y] = xy-yx` in a ring. -/
def commutator {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- A pair satisfying the first Weyl-algebra relation, in the orientation
`[y,x]=1`. -/
def IsWeylPair {A : Type*} [Ring A] (x y : A) : Prop :=
  commutator y x = 1

/-- Evaluation of an affine linear expression at two elements of a rational
algebra.  The ambient algebra need not be commutative. -/
def affineImage {A : Type*} [Ring A] [Algebra ℚ A]
    (a b c : ℚ) (x y : A) : A :=
  a • x + b • y + c • 1

/-- The two-variable affine polynomial map with coefficient matrix
`!![a,b; d,e]`. -/
noncomputable def affinePolynomialMap (a b c d e f : ℚ) :
    Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => C a * X 0 + C b * X 1 + C c
  | 1 => C d * X 0 + C e * X 1 + C f

/-- The polynomial Jacobian matrix of a two-variable polynomial map. -/
noncomputable def polynomialJacobian
    (F : Fin 2 → MvPolynomial (Fin 2) ℚ) :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℚ) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The polynomial Jacobian determinant. -/
noncomputable def jacobianDeterminant
    (F : Fin 2 → MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 2) ℚ :=
  (polynomialJacobian F).det





end JacobianConjecture.AffineWeylBridge


