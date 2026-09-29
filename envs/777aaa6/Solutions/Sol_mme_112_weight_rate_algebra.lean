-- Prove2me | solution 1 for mme_112_weight_rate_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:44.342298+00:00
-- url     : https://prove2.me/submissions/6f1b4d9a-c223-48cd-8901-caba5af85b32

import Definitions.Def_mme_region_count_entropy_data
import Definitions.Def_mme_regional_entropy_rate_data
import Mathlib

open MME MME.RegionRate
open scoped BigOperators

/-- The actual 112 copy and dimension exponents equal a single entropy rate
at their physical scale. The loss remains explicit. -/
theorem solution (D a m : ℕ) (hD : 0 < D) (ha : 2 * a ≤ D)
    (tau delta : ℝ) :
    let p : ℝ := (a : ℝ) / D
    ((4 * (D * m) : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
      ((6 * (4 * ((D - 2 * a) * m) + 2 * ((2 * a) * m)) : ℕ) : ℝ) * tau * Real.log 5 =
    ((D * m : ℕ) : ℝ) *
      (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2 - delta) +
        24 * (1 - p) * tau * Real.log 5) := by
  intro p
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have he : Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] =
      entropy ![p, p, 1 - 2 * p] := by
    simp only [mme_modern_entropyBits, entropy]
    field_simp
  rw [mul_add, he]
  push_cast [Nat.cast_sub ha]
  dsimp [p]
  field_simp
  ring


#print axioms solution
