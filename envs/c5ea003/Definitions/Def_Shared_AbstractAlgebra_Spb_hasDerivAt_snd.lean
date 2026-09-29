-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_Spb_hasDerivAt_snd
-- name    : Shared_AbstractAlgebra_Spb_hasDerivAt_snd
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:27.176527+00:00
-- url     : https://prove2.me/theorems/974e79f4-acac-4c1b-88b2-8feb3b53bdac
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_Spb_hasDerivAt_snd
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.Spb.hasDerivAt.snd`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/Spb_hasDerivAt_snd.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_hasDerivAt_snd

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 8
-/

noncomputable section

/-- The speed-addition law `spb x y = (x + y) / (1 - x y)`. -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)












end


