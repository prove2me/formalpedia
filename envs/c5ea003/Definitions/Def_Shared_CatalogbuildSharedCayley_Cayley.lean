-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedCayley_Cayley
-- name    : Shared_CatalogbuildSharedCayley_Cayley
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:47:54.449289+00:00
-- url     : https://prove2.me/theorems/97714ddf-4fa5-4d6e-8e4b-941c817e4e03
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedCayley_Cayley
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedCayley.Cayley`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedCayley/Cayley.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Cayley

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 2
-/

noncomputable section

/-- The Cayley transform maps a real number to a point on the unit circle
in the complex plane: `cayley(x) = (1 + ix)/(1 - ix)`. -/
def cayley (x : ℝ) : ℂ := (1 + x * Complex.I) / (1 - x * Complex.I)


end


