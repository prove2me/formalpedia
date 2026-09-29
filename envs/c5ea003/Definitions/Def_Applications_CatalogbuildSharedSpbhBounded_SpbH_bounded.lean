-- Prove2me | Definitions.Def_Applications_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Applications_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:49.065588+00:00
-- url     : https://prove2.me/theorems/b677ead9-2aa7-4310-a813-93f83aa76c6a
-- title:
--   Aether Catalog definitions — Applications_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic speed-addition law `spbH u v = (u + v) / (1 + u·v)`. -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)





end


