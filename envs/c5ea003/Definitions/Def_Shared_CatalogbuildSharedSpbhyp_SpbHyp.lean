-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSpbhyp_SpbHyp
-- name    : Shared_CatalogbuildSharedSpbhyp_SpbHyp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:00.273735+00:00
-- url     : https://prove2.me/theorems/7bc2421f-a2b4-4fd6-8496-8ce80c8fb0be
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSpbhyp_SpbHyp
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSpbhyp.SpbHyp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSpbhyp/SpbHyp.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbHyp

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 6
-/

noncomputable section

/-- The hyperbolic SPB (Einstein velocity addition). -/
def spbHyp (x y : ℝ) : ℝ := (x + y) / (1 + x * y)






end


