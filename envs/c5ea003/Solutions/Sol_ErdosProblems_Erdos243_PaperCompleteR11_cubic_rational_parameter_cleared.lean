-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_rational_parameter_cleared
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:29.434913+00:00
-- url     : https://prove2.me/submissions/a8ed670e-df53-4d99-8e02-b4c929b22212

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

/-!
# From an actual rational parameter to the integer scale

The numerator and denominator are obtained from the rational itself. In
particular, coprimality and positivity are proved here, not supplied as
additional assumptions on a purported parametrisation.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) :
    m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs^3 * w.den ∨
      m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs * w.den^3 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hm0 : (m : ℚ) ≠ 0 := ne_of_gt hmpos
  have hspos : (0 : ℚ) < (w.den : ℚ) := by exact_mod_cast w.den_pos
  have hs0 : (w.den : ℚ) ≠ 0 := ne_of_gt hspos
  have hcabs : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hn : |(w.num : ℚ)| = (w.num.natAbs : ℚ) := by
    cases hnum : w.num with
    | ofNat n => simp
    | negSucc n =>
        rw [abs_of_nonpos]
        · norm_num
        · have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
          norm_num
          linarith
  have habs : |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den w]
    rw [abs_div, hn, abs_of_pos hspos]
  have hleft : 0 < w^2 + 1 := by positivity
  rcases heq with heq | heq
  · left
    have hh := congrArg abs heq
    have habsEq : (|w|^2 + 1)^2 = 8 * (6/(m : ℚ)) * |w|^3 := by
      simpa only [abs_pow, abs_of_pos hleft, abs_mul, abs_div, hcabs,
        abs_of_pos hmpos, abs_of_pos (by norm_num : (0 : ℚ) < 8),
        abs_of_pos (by norm_num : (0 : ℚ) < 6), mul_one, sq_abs] using hh
    rw [habs] at habsEq
    field_simp [hm0, hs0] at habsEq
    have hrational : (m : ℚ) * ((w.num.natAbs : ℚ)^2 + (w.den : ℚ)^2)^2 =
        48 * (w.num.natAbs : ℚ)^3 * (w.den : ℚ) := by
      nlinarith [habsEq]
    exact_mod_cast hrational
  · right
    have hh := congrArg abs heq
    have habsEq : (|w|^2 + 1)^2 = 8 * (6/(m : ℚ)) * |w| := by
      simpa only [abs_pow, abs_of_pos hleft, abs_mul, abs_div, hcabs,
        abs_of_pos hmpos, abs_of_pos (by norm_num : (0 : ℚ) < 8),
        abs_of_pos (by norm_num : (0 : ℚ) < 6), mul_one, sq_abs] using hh
    rw [habs] at habsEq
    field_simp [hm0, hs0] at habsEq
    have hrational : (m : ℚ) * ((w.num.natAbs : ℚ)^2 + (w.den : ℚ)^2)^2 =
        48 * (w.num.natAbs : ℚ) * (w.den : ℚ)^3 := by
      nlinarith [habsEq]
    exact_mod_cast hrational
