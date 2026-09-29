-- Prove2me | Theorems.Thm_StereographicCapacityContrarian_s2_proposed_bound_of_area_bound
-- name    : StereographicCapacityContrarian.s2_proposed_bound_of_area_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:51.294018+00:00
-- url     : https://prove2.me/theorems/d6b63130-fb12-4007-8b78-5d6b03e21ae2
-- title:
--   On the range where it is defined, the proposed bound follows from the stronger
-- statement:
--   On the range where it is defined, the proposed bound follows from the stronger
--   area bound; stereographic projection is not needed for this implication.
--
--   ```lean
--   theorem StereographicCapacityContrarian.s2_proposed_bound_of_area_bound(r card : ℝ)
--       (hr : 0 < r) (hrhalf : r < Real.pi / 2)
--       (harea : card ≤ 2 / (1 - Real.cos r)) :
--       card ≤ proposedCorrection r * (sphereArea / capArea r) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/StereographicCapacity/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/StereographicCapacity/Contrarian.lean#L87

-- Thm stub generated from Geometry/StereographicCapacity/Contrarian.lean
import Mathlib
import Definitions.Def_Geometry_StereographicCapacity_Contrarian

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

open StereographicCapacityContrarian

noncomputable section

theorem StereographicCapacityContrarian.s2_proposed_bound_of_area_bound(r card : ℝ)
    (hr : 0 < r) (hrhalf : r < Real.pi / 2)
    (harea : card ≤ 2 / (1 - Real.cos r)) :
    card ≤ proposedCorrection r * (sphereArea / capArea r) := by sorry
