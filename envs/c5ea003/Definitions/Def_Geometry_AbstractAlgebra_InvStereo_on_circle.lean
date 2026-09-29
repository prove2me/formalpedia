-- Prove2me | Definitions.Def_Geometry_AbstractAlgebra_InvStereo_on_circle
-- name    : Geometry_AbstractAlgebra_InvStereo_on_circle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:34:14.399611+00:00
-- url     : https://prove2.me/theorems/061c4106-f92c-4f4a-8b89-03fa844dc1aa
-- title:
--   Aether Catalog definitions — Geometry_AbstractAlgebra_InvStereo_on_circle
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AbstractAlgebra.InvStereo.on.circle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AbstractAlgebra/InvStereo_on_circle.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.InvStereo_on_circle

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- Inverse stereographic projection: ℝ → S¹ ⊂ ℝ².
The encoding: a massive particle's state t maps to a photon state on S¹. -/
def invStereo (t : ℝ) : ℝ × ℝ :=
  (2 * t / (1 + t ^ 2), (1 - t ^ 2) / (1 + t ^ 2))



end


