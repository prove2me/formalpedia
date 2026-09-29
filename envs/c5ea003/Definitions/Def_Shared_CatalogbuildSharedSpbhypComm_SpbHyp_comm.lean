-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- name    : Shared_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:11.45316+00:00
-- url     : https://prove2.me/theorems/919f5109-81f5-41de-8184-6b14979f0261
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSpbhypComm.SpbHyp.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSpbhypComm/SpbHyp_comm.lean by skeleton subtraction
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


