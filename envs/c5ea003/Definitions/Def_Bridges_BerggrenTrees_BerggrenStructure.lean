-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_BerggrenStructure
-- name    : Bridges_BerggrenTrees_BerggrenStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:48.750097+00:00
-- url     : https://prove2.me/theorems/a9dadfda-0eb7-400b-bba8-a505bcf47a7f
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_BerggrenStructure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.BerggrenStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/BerggrenStructure.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.BerggrenStructure

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 20
-/

noncomputable section

/-- Berggren transformation M₁ -/
def berggrenM1 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)

/-- Berggren transformation M₂ -/
def berggrenM2 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)

/-- Berggren transformation M₃ -/
def berggrenM3 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)


















end


