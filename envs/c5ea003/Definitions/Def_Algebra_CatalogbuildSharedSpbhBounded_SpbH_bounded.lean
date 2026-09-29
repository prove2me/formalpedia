-- Prove2me | Definitions.Def_Algebra_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Algebra_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:41.057862+00:00
-- url     : https://prove2.me/theorems/e4712742-7791-42b8-b540-be86105d89ea
-- title:
--   Aether Catalog definitions — Algebra_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

Repaired: the hyperbolic SPB operation `spbH` is defined here.
-/

noncomputable section

/-- The hyperbolic SPB operation `spbH u v = (u + v) / (1 + u * v)`. -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)




end


