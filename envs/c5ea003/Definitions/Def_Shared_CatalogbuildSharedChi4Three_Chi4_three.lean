-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedChi4Three_Chi4_three
-- name    : Shared_CatalogbuildSharedChi4Three_Chi4_three
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:47:56.076108+00:00
-- url     : https://prove2.me/theorems/9b9e0e13-d0a3-441e-ae9f-8102764efea4
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedChi4Three_Chi4_three
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedChi4Three.Chi4.three`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedChi4Three/Chi4_three.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Chi4_three

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 4
-/


noncomputable section

/-- The character χ_{-4}. -/
def chi4 (n : ℤ) : ℤ :=
  if n % 2 = 0 then 0
  else if n % 4 = 1 then 1
  else -1




end


