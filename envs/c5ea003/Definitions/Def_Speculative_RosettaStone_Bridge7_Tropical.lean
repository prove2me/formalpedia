-- Prove2me | Definitions.Def_Speculative_RosettaStone_Bridge7_Tropical
-- name    : Speculative_RosettaStone_Bridge7_Tropical
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:47.463115+00:00
-- url     : https://prove2.me/theorems/7c020500-ae68-4d20-8fa7-ba380d49009f
-- title:
--   Aether Catalog definitions — Speculative_RosettaStone_Bridge7_Tropical
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.RosettaStone.Bridge7.Tropical`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/RosettaStone/Bridge7_Tropical.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.RosettaStone.Bridge7_Tropical

Auto-generated from theorem catalog database.
Domain: Speculative/RosettaStone
Declarations: 9
-/




/-- Tropical determinant of a 2×2 matrix. -/
def tropical_det_2x2 (a b c d : ℝ) : ℝ := min (a + d) (b + c)


