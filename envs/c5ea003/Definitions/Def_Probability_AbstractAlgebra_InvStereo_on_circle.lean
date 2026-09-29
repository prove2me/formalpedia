-- Prove2me | Definitions.Def_Probability_AbstractAlgebra_InvStereo_on_circle
-- name    : Probability_AbstractAlgebra_InvStereo_on_circle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:12.476978+00:00
-- url     : https://prove2.me/theorems/a18061db-0e7d-4f6f-aa52-ab23d2d601ec
-- title:
--   Aether Catalog definitions — Probability_AbstractAlgebra_InvStereo_on_circle
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AbstractAlgebra.InvStereo.on.circle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AbstractAlgebra/InvStereo_on_circle.lean by skeleton subtraction
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


