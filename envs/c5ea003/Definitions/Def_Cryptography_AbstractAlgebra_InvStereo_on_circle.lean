-- Prove2me | Definitions.Def_Cryptography_AbstractAlgebra_InvStereo_on_circle
-- name    : Cryptography_AbstractAlgebra_InvStereo_on_circle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:02:46.749879+00:00
-- url     : https://prove2.me/theorems/9a443ab3-4cc9-46f4-8ed4-ac7c3c5f07f3
-- title:
--   Aether Catalog definitions — Cryptography_AbstractAlgebra_InvStereo_on_circle
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AbstractAlgebra.InvStereo.on.circle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AbstractAlgebra/InvStereo_on_circle.lean by skeleton subtraction
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


