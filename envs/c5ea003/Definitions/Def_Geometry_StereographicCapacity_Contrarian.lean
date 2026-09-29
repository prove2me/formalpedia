-- Prove2me | Definitions.Def_Geometry_StereographicCapacity_Contrarian
-- name    : Geometry_StereographicCapacity_Contrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:51.195049+00:00
-- url     : https://prove2.me/theorems/596105fa-8791-4354-8ce5-a56650ec58a7
-- title:
--   Aether Catalog definitions — Geometry_StereographicCapacity_Contrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.StereographicCapacity.Contrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/StereographicCapacity/Contrarian.lean by skeleton subtraction
import Mathlib

/-!
# Contrarian results for stereographic capacity on `S²`

This self-contained file separates the area argument from the proposed stereographic
correction and tests the claimed calibrations.  Caps of geodesic radius `r` have
area `2π(1-cos r)`.  Pairwise disjoint caps therefore satisfy the stronger direct
area bound `card ≤ 2/(1-cos r)`.

The proposed correction `(2/cos r)^2` does not tend to one: at `r = 0` it equals
four.  Moreover, four caps of radius `π/3` cannot be packed.  Their centers would
be unit vectors with every mutual inner product at most `cos(2π/3) = -1/2`, which
contradicts nonnegativity of the squared norm of their sum.  Thus the advertised
"tetrahedral" calibration is false for caps of that radius.
-/

open scoped ENNReal
open MeasureTheory Set Finset Real

namespace StereographicCapacityContrarian

noncomputable section

/-- Surface area of the unit two-sphere. -/
def sphereArea : ℝ := 4 * Real.pi

/-- Area of a geodesic cap of radius `r` on the unit two-sphere. -/
def capArea (r : ℝ) : ℝ := 2 * Real.pi * (1 - Real.cos r)

/-- The conjectured two-dimensional stereographic correction factor. -/
def proposedCorrection (r : ℝ) : ℝ := (2 / Real.cos r) ^ 2









end

end StereographicCapacityContrarian


