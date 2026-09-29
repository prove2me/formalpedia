-- Prove2me | Definitions.Def_Cryptography_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- name    : Cryptography_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:04.897377+00:00
-- url     : https://prove2.me/theorems/a62657c1-78b3-4b03-8d91-f4b3720c2d52
-- title:
--   Aether Catalog definitions — Cryptography_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.CatalogbuildSharedRootIsPyth.Root.is.pyth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/CatalogbuildSharedRootIsPyth/Root_is_pyth.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Root_is_pyth

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

noncomputable section

/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


end


