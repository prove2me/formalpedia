-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_InvStereo_on_circle
-- name    : Shared_AbstractAlgebra_InvStereo_on_circle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:34.620994+00:00
-- url     : https://prove2.me/theorems/8aaec377-22e0-4e45-8698-6b85df8cdec3
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_InvStereo_on_circle
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.InvStereo.on.circle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/InvStereo_on_circle.lean by skeleton subtraction
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


