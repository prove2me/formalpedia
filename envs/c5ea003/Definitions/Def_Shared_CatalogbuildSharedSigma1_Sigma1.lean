-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSigma1_Sigma1
-- name    : Shared_CatalogbuildSharedSigma1_Sigma1
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:53.590472+00:00
-- url     : https://prove2.me/theorems/323a645f-d29b-480e-a4f0-f21bab58a225
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSigma1_Sigma1
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSigma1.Sigma1`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSigma1/Sigma1.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sigma1

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 2
-/

/-- [Section: # CatalogBuild.Shared.Sigma1
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 2] -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d


