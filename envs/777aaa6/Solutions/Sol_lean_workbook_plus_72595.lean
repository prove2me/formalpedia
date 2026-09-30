-- Prove2me | solution 1 for lean_workbook_plus_72595
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:22:33.490645+00:00
-- url     : https://prove2.me/submissions/3fb8cf95-36aa-46b8-a227-ea6bcd097342

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

def cubicGap (a b c : ℝ) : ℝ :=
  8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2 -
    4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2)

theorem cubic_gap_between (a b c : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hac : a ≤ c) :
    0 ≤ cubicGap a b c := by
  have hu : 0 ≤ a - b := sub_nonneg.mpr hba
  have hv : 0 ≤ c - a := sub_nonneg.mpr hac
  have h : cubicGap a b c =
      2 * b * ((a - b) - (c - a)) ^ 2 + 4 * b * (a - b) ^ 2 +
      4 * b * (c - a) ^ 2 + 3 * (a - b) * ((a - b) - (c - a)) ^ 2 +
      3 * (a - b) ^ 2 * (c - a) + 2 * (a - b) * (c - a) ^ 2 +
      3 * (c - a) ^ 3 := by unfold cubicGap; ring
  rw [h]
  positivity

private theorem cubic_gap_extreme_identity (a b c : ℝ) :
    cubicGap a b c = 4 * (2 * a + b + c) * ((a - b) * (a - c)) +
      3 * (b + c) * (b - c) ^ 2 := by unfold cubicGap; ring

private theorem cubic_gap_sorted (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hbc : b ≤ c) : 0 ≤ cubicGap a b c := by
  by_cases hab : a ≤ b
  · have hp : 0 ≤ (a - b) * (a - c) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab) (sub_nonpos.mpr (hab.trans hbc))
    rw [cubic_gap_extreme_identity]
    positivity
  · have hba : b ≤ a := le_of_not_ge hab
    by_cases hac : a ≤ c
    · exact cubic_gap_between a b c hb hba hac
    · have hp : 0 ≤ (a - b) * (a - c) :=
        mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr (le_of_not_ge hac))
      rw [cubic_gap_extreme_identity]
      positivity

theorem cubic_gap_nonnegative (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ cubicGap a b c := by
  rcases le_total b c with hbc | hcb
  · exact cubic_gap_sorted a b c ha hb hc hbc
  · have hsym : cubicGap a b c = cubicGap a c b := by unfold cubicGap; ring
    rw [hsym]
    exact cubic_gap_sorted a c b ha hc hb hcb

theorem solution (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b ≤ a ∧ a ≤ c) :
    8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2 -
      4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2) ≥ 0 :=
  cubic_gap_nonnegative a b c h₀.1.le h₀.2.1.le h₀.2.2.le

#print axioms solution
#print axioms cubic_gap_nonnegative
