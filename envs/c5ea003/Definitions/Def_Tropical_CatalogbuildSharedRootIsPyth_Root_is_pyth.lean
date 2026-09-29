-- Prove2me | Definitions.Def_Tropical_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- name    : Tropical_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:36.323514+00:00
-- url     : https://prove2.me/theorems/e3b1cc6d-b4df-47ae-af9e-8f21c06ba092
-- title:
--   Aether Catalog definitions — Tropical_CatalogbuildSharedRootIsPyth_Root_is_pyth
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CatalogbuildSharedRootIsPyth.Root.is.pyth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CatalogbuildSharedRootIsPyth/Root_is_pyth.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Root_is_pyth

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

noncomputable section

/-- An integer Pythagorean triple. -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


end


