-- Prove2me | solution 1 for lean_workbook_plus_73693
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:19:11.026123+00:00
-- url     : https://prove2.me/submissions/9a0ead94-785d-4b4d-85e0-a972cc05681a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

private theorem ascending_bound (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (a + b + c) ^ 2 ≥
      3 * (min a b * max b c + min b c * max c a + min c a * max a b) := by
  have hac := hab.trans hbc
  simp only [min_eq_left hab, max_eq_right hbc, min_eq_left hbc,
    max_eq_left hac, min_eq_right hac, max_eq_right hab]
  nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

private theorem valley_bound (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    (a + b + c) ^ 2 ≥
      3 * (min a b * max b c + min b c * max c a + min c a * max a b) := by
  have hab := hac.trans hcb
  simp only [min_eq_left hab, max_eq_left hcb, min_eq_right hcb,
    max_eq_left hac, min_eq_right hac, max_eq_right hab]
  nlinarith only [sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg (sub_nonneg.mpr hcb) (sub_nonneg.mpr hac)]

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥
    3 * (min a b * max b c + min b c * max c a + min c a * max a b) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ascending_bound a b c hab hbc
    · rcases le_total a c with hac | hca
      · exact valley_bound a b c hac hcb
      · simpa only [add_assoc, add_left_comm, add_comm] using ascending_bound c a b hca hab
  · rcases le_total a c with hac | hca
    · simpa only [add_assoc, add_left_comm, add_comm] using valley_bound b c a hba hac
    · rcases le_total b c with hbc | hcb
      · simpa only [add_assoc, add_left_comm, add_comm] using ascending_bound b c a hbc hca
      · simpa only [add_assoc, add_left_comm, add_comm] using valley_bound c a b hcb hba

#print axioms solution
