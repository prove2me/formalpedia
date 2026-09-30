-- Prove2me | solution 1 for lean_workbook_plus_79898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:04:54.752145+00:00
-- url     : https://prove2.me/submissions/5cd370ca-0011-4a17-bb41-7f5b1d8544ef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private lemma schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c) ≤
      3 * a * b * c := by
  have h₁ := mul_nonneg (sq_nonneg (a - b)) (show 0 ≤ a + b - c by linarith)
  have h₂ := mul_nonneg hc
    (mul_nonneg (sub_nonneg.mpr (hbc.trans hab)) (sub_nonneg.mpr hbc))
  nlinarith

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (_hab : a + b > c) (_hbc : b + c > a) (_hca : a + c > b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c) ≤
      3 * a * b * c := by
  rcases le_total a b with hab' | hba'
  · rcases le_total b c with hbc' | hcb'
    · nlinarith [schur_ordered c b a hx.1.le hbc' hab']
    · rcases le_total a c with hac' | hca'
      · nlinarith [schur_ordered b c a hx.1.le hcb' hac']
      · nlinarith [schur_ordered b a c hx.2.2.le hab' hca']
  · rcases le_total a c with hac' | hca'
    · nlinarith [schur_ordered c a b hx.2.1.le hac' hba']
    · rcases le_total b c with hbc' | hcb'
      · nlinarith [schur_ordered a c b hx.2.1.le hca' hbc']
      · exact schur_ordered a b c hx.2.2.le hba' hcb'

#print axioms solution
