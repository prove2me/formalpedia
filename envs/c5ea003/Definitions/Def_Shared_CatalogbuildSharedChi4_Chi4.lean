-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedChi4_Chi4
-- name    : Shared_CatalogbuildSharedChi4_Chi4
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:53.194343+00:00
-- url     : https://prove2.me/theorems/5edd7f55-58f5-48d3-9899-cb847799b930
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedChi4_Chi4
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedChi4.Chi4`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedChi4/Chi4.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Chi4

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 4
-/

noncomputable section

/-- The character χ_{-4}. -/
def chi4 (n : ℤ) : ℤ :=
  if n % 2 = 0 then 0
  else if n % 4 = 1 then 1
  else -1




end


