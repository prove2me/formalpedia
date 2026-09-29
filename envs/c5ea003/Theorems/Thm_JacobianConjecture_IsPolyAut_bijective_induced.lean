-- Prove2me | Theorems.Thm_JacobianConjecture_IsPolyAut_bijective_induced
-- name    : JacobianConjecture.IsPolyAut.bijective_induced
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:45:21.561341+00:00
-- url     : https://prove2.me/theorems/a0f7fc8d-9ad8-4554-b670-462588332adf
-- title:
--   Bridge theorem.
-- statement:
--   **Bridge theorem.**  A polynomial automorphism induces a bijection on the
--   points of every `R`-algebra.
--
--   ```lean
--   theorem JacobianConjecture.IsPolyAut.bijective_induced{F G : Fin n → MvPolynomial (Fin n) R}
--       (h : IsPolyAut F G) (A : Type*) [CommRing A] [Algebra R A] :
--       Function.Bijective (induced F (A := A)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/JacobianCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/JacobianCore.lean#L78

-- Thm stub generated from Probability/JacobianCore.lean
import Mathlib
import Definitions.Def_Probability_JacobianCore

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

open JacobianConjecture

variable {n : ℕ} {R : Type*} [CommRing R]

theorem JacobianConjecture.IsPolyAut.bijective_induced{F G : Fin n → MvPolynomial (Fin n) R}
    (h : IsPolyAut F G) (A : Type*) [CommRing A] [Algebra R A] :
    Function.Bijective (induced F (A := A)) := by sorry
