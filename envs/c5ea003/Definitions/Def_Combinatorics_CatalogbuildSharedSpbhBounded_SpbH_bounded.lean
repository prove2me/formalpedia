-- Prove2me | Definitions.Def_Combinatorics_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Combinatorics_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:29:10.142358+00:00
-- url     : https://prove2.me/theorems/20fb2919-2652-429c-8395-bae6a69ba255
-- title:
--   Aether Catalog definitions — Combinatorics_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic SPB (relativistic velocity addition) operation
`spbH u v = (u + v)/(1 + u v)`. -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)






end


