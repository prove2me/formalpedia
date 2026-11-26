-- Prove2me | solution 1 for ReweightedNPMLE.log_one_add_sq_le_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:08:25.229611+00:00
-- url     : https://prove2.me/submissions/2d06ac41-caed-41a1-ab7d-1a0757f11df5

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

-- Inline helpers preserved from ReweightedNPMLE.Localization.
section
/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

namespace ReweightedNPMLE



/-- A direct logarithm bound from the convergent Taylor series. -/
theorem abs_log_one_add_le {u : ℝ} (hu : |u| < 1) :
    |Real.log (1 + u)| ≤ |u| / (1 - |u|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 0
  simpa using h









end ReweightedNPMLE
end

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- On the localization ball, the squared log displacement is at most twice the squared one. -/
theorem solution {u : ℝ} (hu : |u| ≤ 1 / 16) :
    Real.log (1 + u) ^ 2 ≤ 2 * u ^ 2 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  have hlog := abs_log_one_add_le hu1
  have hratio : |u| / (1 - |u|) ≤ (16 / 15 : ℝ) * |u| := by
    rw [div_le_iff₀ hden]
    nlinarith [abs_nonneg u]
  have habs : |Real.log (1 + u)| ≤ (16 / 15 : ℝ) * |u| := hlog.trans hratio
  calc
    Real.log (1 + u) ^ 2 = |Real.log (1 + u)| ^ 2 := (sq_abs _).symm
    _ ≤ ((16 / 15 : ℝ) * |u|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
    _ ≤ 2 * u ^ 2 := by
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg u]
