-- Prove2me | Definitions.Def_Tropical_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Tropical_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:42.565571+00:00
-- url     : https://prove2.me/theorems/4bb9f0a9-60ee-42c2-aeb3-e26f866a2319
-- title:
--   Aether Catalog definitions — Tropical_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic SPB operation, `spbH u v = (u + v) / (1 + u * v)`
(the velocity-addition law in units where `c = 1`). -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)




end


