-- Prove2me | Definitions.Def_Probability_JacobianCore
-- name    : Probability_JacobianCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:24.040142+00:00
-- url     : https://prove2.me/theorems/b1169dd8-1cf3-47dc-a0ea-674129e71aeb
-- title:
--   Aether Catalog definitions — Probability_JacobianCore
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.JacobianCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/JacobianCore.lean by skeleton subtraction
import Mathlib

/-!
# Core infrastructure for the Jacobian Conjecture

The three Jacobian-Conjecture files in `Catalog/Probability/` (`DegreeTwo.lean`,
`Druzkowski.lean`, `Counterexamples.lean`) were written against a core module
providing the polynomial Jacobian, polynomial composition, polynomial
automorphisms and the induced map on algebras.  That module was missing from the
catalog (the file `Novelty/Core.lean` that they imported contains an unrelated
development about agreement subtrees).  This file supplies it.

## Main definitions

* `polyJacobian F` — the matrix `(∂Fᵢ/∂Xⱼ)` of a polynomial map.
* `jacDet F` — its determinant.
* `pcomp F G` — the composite polynomial map `F ∘ G`, i.e. `i ↦ F i (G)`.
* `IsPolyAut F G` — `F` and `G` are mutually inverse polynomial maps.
* `induced F` — the map on points of an arbitrary `R`-algebra defined by `F`.

## Main results

* `IsPolyAut.bijective_induced` — a polynomial automorphism induces a bijection
  on the points of every `R`-algebra.  This is the bridge that turns a formal
  polynomial identity into the geometric statement of the conjecture.
-/

open MvPolynomial

namespace JacobianConjecture

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The Jacobian matrix `(∂Fᵢ/∂Xⱼ)` of a polynomial map. -/
noncomputable def polyJacobian (F : Fin n → MvPolynomial (Fin n) R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The Jacobian determinant of a polynomial map. -/
noncomputable def jacDet (F : Fin n → MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  (polyJacobian F).det

/-- Composition of polynomial maps: `pcomp F G` substitutes `G` into `F`. -/
noncomputable def pcomp (F G : Fin n → MvPolynomial (Fin n) R) :
    Fin n → MvPolynomial (Fin n) R :=
  fun i => aeval G (F i)

/-- `F` and `G` are mutually inverse polynomial maps. -/
structure IsPolyAut (F G : Fin n → MvPolynomial (Fin n) R) : Prop where
  comp_left : pcomp F G = X
  comp_right : pcomp G F = X

/-- The map on `A`-points induced by a polynomial map, for any `R`-algebra `A`. -/
noncomputable def induced (F : Fin n → MvPolynomial (Fin n) R)
    {A : Type*} [CommRing A] [Algebra R A] : (Fin n → A) → (Fin n → A) :=
  fun x i => aeval x (F i)






end JacobianConjecture


