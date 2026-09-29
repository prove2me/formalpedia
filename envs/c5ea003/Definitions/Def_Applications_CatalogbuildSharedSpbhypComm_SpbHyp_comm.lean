-- Prove2me | Definitions.Def_Applications_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- name    : Applications_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:56.455768+00:00
-- url     : https://prove2.me/theorems/3f94273f-3317-452f-a518-0071372495cf
-- title:
--   Aether Catalog definitions — Applications_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CatalogbuildSharedSpbhypComm.SpbHyp.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CatalogbuildSharedSpbhypComm/SpbHyp_comm.lean by skeleton subtraction
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


