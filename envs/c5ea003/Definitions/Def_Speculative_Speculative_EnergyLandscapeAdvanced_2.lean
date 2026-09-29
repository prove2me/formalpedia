-- Prove2me | Definitions.Def_Speculative_Speculative_EnergyLandscapeAdvanced_2
-- name    : Speculative_Speculative_EnergyLandscapeAdvanced_2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:35:01.735439+00:00
-- url     : https://prove2.me/theorems/043aca3d-8556-4cff-83ef-75d98896dd6e
-- title:
--   Aether Catalog definitions — Speculative_Speculative_EnergyLandscapeAdvanced_2
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Speculative.EnergyLandscapeAdvanced.2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Speculative/EnergyLandscapeAdvanced_2.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.EnergyLandscapeAdvanced_2

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 9
-/

/-- [Section: # CatalogBuild.Speculative.EnergyLandscapeAdvanced_2
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 9] -/
def E' (N x : ℕ) : ℕ := N % x




def sublevel' (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E' N x ≤ t)


