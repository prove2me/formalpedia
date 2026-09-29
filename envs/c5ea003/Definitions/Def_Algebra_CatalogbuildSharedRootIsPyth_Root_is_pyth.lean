-- Prove2me | Definitions.Def_Algebra_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- name    : Algebra_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:37.165011+00:00
-- url     : https://prove2.me/theorems/c3b92b7b-4a9b-433c-8259-abe1dc8015ba
-- title:
--   Aether Catalog definitions — Algebra_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CatalogbuildSharedRootIsPyth.Root.is.pyth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CatalogbuildSharedRootIsPyth/Root_is_pyth.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Root_is_pyth

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1

Repaired: the predicate `IsPythTriple` is defined here (the module never
imported the file that declares it).
-/

noncomputable section

/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


end


