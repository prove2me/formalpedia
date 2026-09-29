-- Prove2me | Definitions.Def_EML_EML_TropicalSPB
-- name    : EML_EML_TropicalSPB
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:21.244748+00:00
-- url     : https://prove2.me/theorems/ffb0e3a7-e2c0-43dc-9a31-9be7191b0dc3
-- title:
--   Aether Catalog definitions — EML_EML_TropicalSPB
-- statement:
--   Definition bundle for the Aether Catalog module `EML.EML.TropicalSPB`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/EML/TropicalSPB.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.TropicalSPB

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 6
-/

noncomputable section

/-- The tropical SPB: replaces + with min and × with +.
tspb(x, y) = min(x, y) - max(0, x + y)
Motivation: In standard SPB, spb(x,y) = (x+y)/(1-xy).
Tropicalizing: numerator x+y → min(x,y), denominator 1-xy → min(0, -(x+y)) = -max(0, x+y).
Division → subtraction, so tspb(x,y) = min(x,y) - max(0, x+y). -/
def tropSPB (x y : ℝ) : ℝ := min x y - max 0 (x + y)



/-- Alternative tropical SPB using max instead of min:
tspb_max(x, y) = max(x, y) - max(0, x + y). -/
def tropSPBMax (x y : ℝ) : ℝ := max x y - max 0 (x + y)



end


