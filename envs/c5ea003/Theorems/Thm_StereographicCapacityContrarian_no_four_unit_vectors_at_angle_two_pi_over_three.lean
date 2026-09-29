-- Prove2me | Theorems.Thm_StereographicCapacityContrarian_no_four_unit_vectors_at_angle_two_pi_over_three
-- name    : StereographicCapacityContrarian.no_four_unit_vectors_at_angle_two_pi_over_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:18.968721+00:00
-- url     : https://prove2.me/theorems/0e00ea6e-b5cc-4a07-946b-0d4cffdf57b7
-- title:
--   Four unit vectors cannot all have mutual inner product at most `-1/2`.
-- statement:
--   Four unit vectors cannot all have mutual inner product at most `-1/2`.
--   This is the Gram-matrix obstruction behind the failure of the `π/3` tetrahedral test.
--
--   ```lean
--   theorem StereographicCapacityContrarian.no_four_unit_vectors_at_angle_two_pi_over_three    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       (a b c d : E)
--       (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
--       (hab : inner ℝ a b ≤ -(1 / 2 : ℝ))
--       (hac : inner ℝ a c ≤ -(1 / 2 : ℝ))
--       (had : inner ℝ a d ≤ -(1 / 2 : ℝ))
--       (hbc : inner ℝ b c ≤ -(1 / 2 : ℝ))
--       (hbd : inner ℝ b d ≤ -(1 / 2 : ℝ))
--       (hcd : inner ℝ c d ≤ -(1 / 2 : ℝ)) : False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/StereographicCapacity/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/StereographicCapacity/Contrarian.lean#L127

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

theorem StereographicCapacityContrarian.no_four_unit_vectors_at_angle_two_pi_over_three    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c d : E)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : inner ℝ a b ≤ -(1 / 2 : ℝ))
    (hac : inner ℝ a c ≤ -(1 / 2 : ℝ))
    (had : inner ℝ a d ≤ -(1 / 2 : ℝ))
    (hbc : inner ℝ b c ≤ -(1 / 2 : ℝ))
    (hbd : inner ℝ b d ≤ -(1 / 2 : ℝ))
    (hcd : inner ℝ c d ≤ -(1 / 2 : ℝ)) : False := by sorry
