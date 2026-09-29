-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedIspythtriple_IsPythTriple
-- name    : Shared_CatalogbuildSharedIspythtriple_IsPythTriple
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:50.892645+00:00
-- url     : https://prove2.me/theorems/99ad670d-158f-4a02-9a2f-36ba3a54ecd8
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedIspythtriple_IsPythTriple
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedIspythtriple.IsPythTriple`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedIspythtriple/IsPythTriple.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.IsPythTriple

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

noncomputable section

/-- A Pythagorean triple over integers. -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

end


