-- Prove2me | solution 1 for lean_workbook_plus_77123
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:02.501616+00:00
-- url     : https://prove2.me/submissions/828ce044-1d90-403d-ac3e-472220493bba

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

private theorem ordered_polynomial (a b c : ℝ) (hc : 0 ≤ c)
    (hab : b ≤ a) (hbc : c ≤ b) :
    0 ≤ (a + b + c) * (a * b + b * c + c * a) ^ 2 -
      4 * (a + b + c) ^ 2 * (a * b * c) +
      3 * (a * b + b * c + c * a) * (a * b * c) := by
  let x := a - b
  let y := b - c
  have hx : 0 ≤ x := sub_nonneg.mpr hab
  have hy : 0 ≤ y := sub_nonneg.mpr hbc
  have ha' : a = x + y + c := by dsimp [x, y]; ring
  have hb' : b = y + c := by dsimp [y]; ring
  rw [ha', hb']
  clear_value x y
  convert (show (0 : ℝ) ≤ x ^ 3 * y ^ 2 +
    x ^ 2 * (4 * y ^ 3 + 6 * y ^ 2 * c + 3 * y * c ^ 2 + 2 * c ^ 3) +
    x * y * (5 * y ^ 3 + 12 * y ^ 2 * c + 9 * y * c ^ 2 + 2 * c ^ 3) +
    2 * y ^ 2 * (y + c) ^ 3 by positivity) using 1 <;> ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥
      4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 5 := by
  have hq : 0 < a * b + b * c + a * c := by positivity
  have hpoly : 0 ≤ (a + b + c) * (a * b + b * c + c * a) ^ 2 -
      4 * (a + b + c) ^ 2 * (a * b * c) +
      3 * (a * b + b * c + c * a) * (a * b * c) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      · nlinarith [ordered_polynomial c b a ha.le hbc hab]
      · rcases le_total a c with hac | hca
        · nlinarith [ordered_polynomial b c a ha.le hcb hac]
        · nlinarith [ordered_polynomial b a c hc.le hab hca]
    · rcases le_total a c with hac | hca
      · nlinarith [ordered_polynomial c a b hb.le hac hba]
      · rcases le_total b c with hbc | hcb
        · nlinarith [ordered_polynomial a c b hb.le hca hbc]
        · exact ordered_polynomial a b c hc.le hba hcb
  have identity :
      ((a + b + c) * (1 / a + 1 / b + 1 / c) -
        (4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 5)) *
        ((a * b * c) * (a * b + b * c + a * c)) =
      (a + b + c) * (a * b + b * c + c * a) ^ 2 -
        4 * (a + b + c) ^ 2 * (a * b * c) +
        3 * (a * b + b * c + c * a) * (a * b * c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hq]
    <;> ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := (a * b * c) * (a * b + b * c + a * c))
    (by rw [identity]; exact hpoly) (by positivity)

#print axioms solution
