-- Prove2me | Definitions.Def_Probability_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Probability_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:55.126288+00:00
-- url     : https://prove2.me/theorems/f3e1ac76-2d28-44ef-8a05-59f0d9e0d710
-- title:
--   Aether Catalog definitions — Probability_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic SPB (Einstein velocity addition law): `spbH u v = (u+v)/(1+uv)`.
(The auto-generated catalog file used this definition without stating it.) -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)




end


