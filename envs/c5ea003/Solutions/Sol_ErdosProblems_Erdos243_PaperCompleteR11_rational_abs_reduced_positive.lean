-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.rational_abs_reduced_positive
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:55:52.203664+00:00
-- url     : https://prove2.me/submissions/6601d134-b7b1-4e03-af99-8fb8804232d8

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
theorem solution (w : ℚ) (hw : w ≠ 0) :
    0 < w.num.natAbs ∧ 0 < w.den ∧
      Nat.Coprime w.num.natAbs w.den ∧
      |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by
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
    rw [abs_div, hn, abs_of_pos (by exact_mod_cast w.den_pos)]
  have hr : 0 < w.num.natAbs := by
    by_contra h
    have hz : w.num.natAbs = 0 := by omega
    have hz' : |w| = 0 := by simpa [hz] using habs
    exact hw (abs_eq_zero.mp hz')
  exact ⟨hr, w.den_pos, w.reduced, habs⟩
