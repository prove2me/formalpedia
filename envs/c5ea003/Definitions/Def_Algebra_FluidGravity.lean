-- Prove2me | Definitions.Def_Algebra_FluidGravity
-- name    : Algebra_FluidGravity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:18.695659+00:00
-- url     : https://prove2.me/theorems/7caf4d31-f27c-43ff-b683-4b993d3ccc25
-- title:
--   Aether Catalog definitions — Algebra_FluidGravity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.FluidGravity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/FluidGravity.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.Spacetime.FluidGravity

Auto-generated from theorem catalog database.
Domain: Physics/Spacetime
Declarations: 20
-/

noncomputable section













def pageEntropy (t S_BH : ℝ) : ℝ := min t (S_BH - t)




def blackeningFactor (r rH : ℝ) (d : ℕ) : ℝ := 1 - (rH / r) ^ d




end


