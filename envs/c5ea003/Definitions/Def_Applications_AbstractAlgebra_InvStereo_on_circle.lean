-- Prove2me | Definitions.Def_Applications_AbstractAlgebra_InvStereo_on_circle
-- name    : Applications_AbstractAlgebra_InvStereo_on_circle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:02:14.867051+00:00
-- url     : https://prove2.me/theorems/19658d69-91e4-41f2-87c5-914c863756fb
-- title:
--   Aether Catalog definitions — Applications_AbstractAlgebra_InvStereo_on_circle
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AbstractAlgebra.InvStereo.on.circle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AbstractAlgebra/InvStereo_on_circle.lean by skeleton subtraction
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


