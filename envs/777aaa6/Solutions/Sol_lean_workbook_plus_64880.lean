-- Prove2me | solution 1 for lean_workbook_plus_64880
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:18.898811+00:00
-- url     : https://prove2.me/submissions/e48a791d-45a0-4aaf-a820-f9e5868014aa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem ordered_bound (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥
      3 * |a - b| * |b - c| * |c - a| := by
  have hu : 0 ≤ b - a := sub_nonneg.mpr hab
  have hv : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hr : 0 ≤ 3 * a * ((b - a) ^ 2 + (b - a) * (c - b) + (c - b) ^ 2) +
      2 * (b - a) ^ 3 + (c - b) ^ 3 := by positivity
  rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hbc),
    abs_of_nonneg (sub_nonneg.mpr (hab.trans hbc))]
  nlinarith only [hr]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥
      3 * |(a - b) * (b - c) * (c - a)| := by
  rw [abs_mul, abs_mul]
  rcases le_total a b with hab | hba <;>
    rcases le_total b c with hbc | hcb <;>
    rcases le_total a c with hac | hca
  all_goals first
    | have h := ordered_bound a b c ha.le hab hbc
    | have h := ordered_bound a c b ha.le hac hcb
    | have h := ordered_bound b a c hb.le hba hac
    | have h := ordered_bound b c a hb.le hbc hca
    | have h := ordered_bound c a b hc.le hca hab
    | have h := ordered_bound c b a hc.le hcb hba
  all_goals
    simpa only [abs_sub_comm, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
