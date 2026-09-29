-- Prove2me | Definitions.Def_Logic_Cayley
-- name    : Logic_Cayley
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:48:44.646838+00:00
-- url     : https://prove2.me/theorems/f96ec2ab-6fcb-4b0b-8c1f-4cb22d3e4257
-- title:
--   Aether Catalog definitions — Logic_Cayley
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Cayley`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Cayley.lean by skeleton subtraction
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


