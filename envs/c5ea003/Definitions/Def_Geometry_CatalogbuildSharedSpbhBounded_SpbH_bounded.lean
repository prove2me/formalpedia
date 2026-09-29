-- Prove2me | Definitions.Def_Geometry_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Geometry_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:52:52.945863+00:00
-- url     : https://prove2.me/theorems/258fd429-ef0b-46f5-acc3-20de7e395e5b
-- title:
--   Aether Catalog definitions — Geometry_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic speed-addition law `spbH u v = (u + v) / (1 + u v)`. -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)




end


