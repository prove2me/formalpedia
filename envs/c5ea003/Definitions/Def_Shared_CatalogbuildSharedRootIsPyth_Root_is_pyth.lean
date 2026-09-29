-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- name    : Shared_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:09.764417+00:00
-- url     : https://prove2.me/theorems/5005f902-b8c2-4062-913e-0db93fa80606
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedRootIsPyth.Root.is.pyth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedRootIsPyth/Root_is_pyth.lean by skeleton subtraction
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


