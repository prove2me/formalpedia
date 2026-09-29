-- Prove2me | Definitions.Def_Speculative_Energylandscapeadvanced2_EnergyLandscapeAdvanced_2
-- name    : Speculative_Energylandscapeadvanced2_EnergyLandscapeAdvanced_2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:06.481064+00:00
-- url     : https://prove2.me/theorems/19eae728-d2cc-48b0-af55-5cd044afd9f8
-- title:
--   Aether Catalog definitions — Speculative_Energylandscapeadvanced2_EnergyLandscapeAdvanced_2
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Energylandscapeadvanced2.EnergyLandscapeAdvanced.2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Energylandscapeadvanced2/EnergyLandscapeAdvanced_2.lean by skeleton subtraction
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


