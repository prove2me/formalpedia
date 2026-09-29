-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedTribonacci_Tribonacci
-- name    : Shared_CatalogbuildSharedTribonacci_Tribonacci
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:00.925737+00:00
-- url     : https://prove2.me/theorems/6301519e-db27-45b7-b9f8-afc8951022e2
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedTribonacci_Tribonacci
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedTribonacci.Tribonacci`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedTribonacci/Tribonacci.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Tribonacci

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 2
-/

/-- [Section: # CatalogBuild.Shared.Tribonacci
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 2] -/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n


