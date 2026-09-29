-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_Euclid_parametrization
-- name    : Algebra_AbstractAlgebra_Euclid_parametrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:04:49.909987+00:00
-- url     : https://prove2.me/theorems/52886726-7f8f-4baa-80d0-0c38e9cd9e2f
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_Euclid_parametrization
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.Euclid.parametrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/Euclid_parametrization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Euclid_parametrization

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1

Repaired: the predicate `IsPythTriple'` used by the statement was never defined
in the catalog; it is supplied here with its intended meaning.
-/

noncomputable section

/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPythTriple' (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


end


