-- Prove2me | Definitions.Def_Algebra_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- name    : Algebra_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:42.265841+00:00
-- url     : https://prove2.me/theorems/060fe285-b7dd-434f-97ef-6b4b0ff7362f
-- title:
--   Aether Catalog definitions — Algebra_CatalogbuildSharedSpbhypComm_SpbHyp_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CatalogbuildSharedSpbhypComm.SpbHyp.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CatalogbuildSharedSpbhypComm/SpbHyp_comm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbHyp_comm

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 6

Repaired: `import` moved to the top and `spbHyp` placed before its uses.
-/

noncomputable section

/-- The hyperbolic SPB (Einstein velocity addition). -/
def spbHyp (x y : ℝ) : ℝ := (x + y) / (1 + x * y)






end


