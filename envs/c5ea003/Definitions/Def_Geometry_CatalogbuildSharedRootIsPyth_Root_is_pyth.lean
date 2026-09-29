-- Prove2me | Definitions.Def_Geometry_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- name    : Geometry_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:52:49.760597+00:00
-- url     : https://prove2.me/theorems/e00292ea-51fb-4c15-88c3-4d0e5d190218
-- title:
--   Aether Catalog definitions — Geometry_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CatalogbuildSharedRootIsPyth.Root.is.pyth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CatalogbuildSharedRootIsPyth/Root_is_pyth.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Root_is_pyth

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

noncomputable section

/-- A Pythagorean triple. -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


end


