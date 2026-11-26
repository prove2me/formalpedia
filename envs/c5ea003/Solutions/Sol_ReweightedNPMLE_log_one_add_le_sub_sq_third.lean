-- Prove2me | solution 1 for ReweightedNPMLE.log_one_add_le_sub_sq_third
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:38.239733+00:00
-- url     : https://prove2.me/submissions/61bdc7d3-d906-491f-9a72-08c8dd874eb2

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set
/-- The upper Taylor bound used to force a near-optimal point into the localization ball. -/
theorem solution {u : ℝ} (hu : |u| ≤ 1 / 4) :
    Real.log (1 + u) ≤ u - u ^ 2 / 3 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  have hseries := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 3
  have hupper := (le_abs_self
    ((∑ i ∈ Finset.range 3, (-u) ^ (i + 1) / (i + 1)) + Real.log (1 - (-u)))).trans
      hseries
  norm_num [Finset.sum_range_succ] at hupper
  have hu_sq : |u| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg u) (by norm_num)).2 hu
  have hrem : |u| ^ 4 / (1 - |u|) ≤ u ^ 2 / 12 := by
    rw [div_le_iff₀ hden]
    rw [show |u| ^ 4 = u ^ 2 * |u| ^ 2 by
      calc
        |u| ^ 4 = |u| ^ 2 * |u| ^ 2 := by ring
        _ = u ^ 2 * |u| ^ 2 := by rw [sq_abs]]
    nlinarith [sq_nonneg u, abs_nonneg u]
  have hcubic : u ^ 3 / 3 ≤ u ^ 2 / 12 := by
    have hu_upper : u ≤ 1 / 4 := (le_abs_self u).trans hu
    nlinarith [sq_nonneg u]
  rw [show (-u) ^ 3 = -(u ^ 3) by ring] at hupper
  linarith
