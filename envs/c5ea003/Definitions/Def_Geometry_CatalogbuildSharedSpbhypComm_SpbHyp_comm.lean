-- Prove2me | Definitions.Def_Geometry_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- name    : Geometry_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:52:58.025334+00:00
-- url     : https://prove2.me/theorems/d3544745-adae-4e10-857a-ecf861244b55
-- title:
--   Aether Catalog definitions — Geometry_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CatalogbuildSharedSpbhypComm.SpbHyp.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CatalogbuildSharedSpbhypComm/SpbHyp_comm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbHyp_comm

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 6
-/


noncomputable section

/-- The hyperbolic SPB (Einstein velocity addition). -/
def spbHyp (x y : ℝ) : ℝ := (x + y) / (1 + x * y)






end


