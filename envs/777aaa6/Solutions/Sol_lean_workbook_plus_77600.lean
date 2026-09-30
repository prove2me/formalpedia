-- Prove2me | solution 1 for lean_workbook_plus_77600
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:06.926292+00:00
-- url     : https://prove2.me/submissions/d9e36f13-0b35-4c22-b656-e9152bc3fb0e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

private theorem ordered_bound (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    3 * a * b * c + (9 / 4) * (|a - b| * |b - c| * |c - a|) ≤
      a ^ 3 + b ^ 3 + c ^ 3 := by
  rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (sub_nonneg.mpr hbc),
    abs_of_nonpos (sub_nonpos.mpr (hbc.trans hab))]
  apply sub_nonneg.mp
  let x := a - b
  let y := b - c
  have hx : 0 ≤ x := sub_nonneg.mpr hab
  have hy : 0 ≤ y := sub_nonneg.mpr hbc
  have ha' : a = x + y + c := by dsimp [x, y]; ring
  have hb' : b = y + c := by dsimp [y]; ring
  rw [ha', hb']
  clear_value x y
  convert (show (0 : ℝ) ≤ x ^ 3 + (3 / 4) * x ^ 2 * y +
    (3 / 4) * x * y ^ 2 + 2 * y ^ 3 + 3 * c * (x ^ 2 + x * y + y ^ 2)
    by positivity) using 1 <;> ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 ≥ 3 * a * b * c + (9 / 4) * |(a - b) * (b - c) * (c - a)| := by
  simp only [abs_mul]
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · have h := ordered_bound c b a ha.le hbc hab
      simp only [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a] at h ⊢
      nlinarith
    · rcases le_total a c with hac | hca
      · have h := ordered_bound b c a ha.le hcb hac
        simp only [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a] at h ⊢
        nlinarith
      · have h := ordered_bound b a c hc.le hab hca
        simp only [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a] at h ⊢
        nlinarith
  · rcases le_total a c with hac | hca
    · have h := ordered_bound c a b hb.le hac hba
      simp only [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a] at h ⊢
      nlinarith
    · rcases le_total b c with hbc | hcb
      · have h := ordered_bound a c b hb.le hca hbc
        simp only [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a] at h ⊢
        nlinarith
      · exact ordered_bound a b c hc.le hba hcb

#print axioms solution
