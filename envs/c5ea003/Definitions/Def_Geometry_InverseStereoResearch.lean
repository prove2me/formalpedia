-- Prove2me | Definitions.Def_Geometry_InverseStereoResearch
-- name    : Geometry_InverseStereoResearch
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:13.996305+00:00
-- url     : https://prove2.me/theorems/2fb8ebfe-1a62-4fc2-8ebf-b415e41e4d44
-- title:
--   Aether Catalog definitions — Geometry_InverseStereoResearch
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.InverseStereoResearch`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/InverseStereoResearch.lean by skeleton subtraction
import Mathlib

open Real

/-! # CatalogBuild.Geometry.Stereographic.InverseStereoResearch

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 44
-/


noncomputable section

/-- Inverse stereographic projection: ℝ → S¹ ⊂ ℝ². -/
def invStereo (t : ℝ) : ℝ × ℝ :=
  (2 * t / (1 + t ^ 2), (1 - t ^ 2) / (1 + t ^ 2))

















































































































































































end


