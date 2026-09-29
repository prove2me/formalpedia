-- Prove2me | Definitions.Def_Speculative_SciFi_AlienLife
-- name    : Speculative_SciFi_AlienLife
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:48.181322+00:00
-- url     : https://prove2.me/theorems/528ab840-c5bf-4e21-9d3c-c8adaaa6d45c
-- title:
--   Aether Catalog definitions — Speculative_SciFi_AlienLife
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.SciFi.AlienLife`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/SciFi/AlienLife.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.SciFi.AlienLife

Auto-generated from theorem catalog database.
Domain: Speculative/SciFi
Declarations: 6
-/

noncomputable section




/-- CDF of the nearest-neighbor distance in a 3D Poisson process. -/
def poissonNearestCDF (ρ r : ℝ) : ℝ :=
  1 - Real.exp (-(4 * Real.pi * ρ * r ^ 3 / 3))



end


