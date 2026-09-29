-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Shared_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:55.025748+00:00
-- url     : https://prove2.me/theorems/f5f13a56-d4b7-45ef-a1c7-4579486d5948
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
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


