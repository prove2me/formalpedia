-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_Spb_zero_right
-- name    : Shared_AbstractAlgebra_Spb_zero_right
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:23.187302+00:00
-- url     : https://prove2.me/theorems/6987ae1c-eb1a-49fc-a041-376cb182e3a6
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_Spb_zero_right
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.Spb.zero.right`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/Spb_zero_right.lean by skeleton subtraction
import Mathlib

open Real

/-! # CatalogBuild.Shared.Spb_zero_right

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 14
-/


noncomputable section

/-- The Cayley transform `cayley x = (1 + x i) / (1 - x i)`. -/
def cayley (x : ℝ) : ℂ := (1 + x * Complex.I) / (1 - x * Complex.I)

/-- The SPB (Stereographic Projection Bridge) operation.
`spb x y = (x + y) / (1 - x * y)` -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)














end


