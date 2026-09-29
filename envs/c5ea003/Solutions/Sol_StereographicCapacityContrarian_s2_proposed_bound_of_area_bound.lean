-- Prove2me | solution 1 for StereographicCapacityContrarian.s2_proposed_bound_of_area_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:10:54.939322+00:00
-- url     : https://prove2.me/submissions/54fc45ab-0b9c-4968-9563-50c417dd2eff

-- Sol generated from Geometry/StereographicCapacity/Contrarian.lean
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














open StereographicCapacityContrarian in
theorem solution(r card : ℝ)
    (hr : 0 < r) (hrhalf : r < Real.pi / 2)
    (harea : card ≤ 2 / (1 - Real.cos r)) :
    card ≤ proposedCorrection r * (sphereArea / capArea r) := by
  rw [proposedCorrection, sphereArea, capArea]
  -- Simplify the fraction 4π / (2π(1 - cos r)) = 2 / (1 - cos r)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hcos_pos : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos_lt_one : Real.cos r < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have h_one_minus_cos_pos : 0 < 1 - Real.cos r := by linarith
  have h_frac : 4 * Real.pi / (2 * Real.pi * (1 - Real.cos r)) = 2 / (1 - Real.cos r) := by
    field_simp
    ring
  rw [h_frac]
  -- Since (2 / cos r)^2 ≥ 1, we have (2/cos r)^2 * (2/(1-cos r)) ≥ 2/(1-cos r)
  have h_one_le : 1 ≤ (2 / Real.cos r) ^ 2 := by
    have hcos_le_one : Real.cos r ≤ 1 := Real.cos_le_one r
    have : 2 / Real.cos r ≥ 1 := by
      have h1 : 2 ≥ Real.cos r := by linarith
      exact (one_le_div hcos_pos).mpr (by linarith)
    nlinarith [sq_nonneg (2 / Real.cos r - 1)]
  calc card ≤ 2 / (1 - Real.cos r) := harea
    _ = 1 * (2 / (1 - Real.cos r)) := by ring
    _ ≤ (2 / Real.cos r) ^ 2 * (2 / (1 - Real.cos r)) := by gcongr
