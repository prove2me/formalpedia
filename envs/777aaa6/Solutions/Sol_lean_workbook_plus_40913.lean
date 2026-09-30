-- Prove2me | solution 1 for lean_workbook_plus_40913
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:22:20.650316+00:00
-- url     : https://prove2.me/submissions/40283fc0-adff-4cc8-bec6-e47c3e77f75d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ)
    (h : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) :
    abs a + abs b + abs c ≤ 3 := by
  have hp : |a + b + c| ≤ 1 := by simpa using h 1 (by constructor <;> norm_num)
  have hm : |a - b + c| ≤ 1 := by simpa using h (-1) (by constructor <;> norm_num)
  have hc : |c| ≤ 1 := by simpa using h 0 (by constructor <;> norm_num)
  have hs : |a + c| + |b| ≤ 1 := by
    rcases le_total 0 (a + c) with hs | hs
    · rw [abs_of_nonneg hs]
      rcases le_total 0 b with hb | hb
      · rw [abs_of_nonneg hb]
        linarith [(abs_le.mp hp).2]
      · rw [abs_of_nonpos hb]
        linarith [(abs_le.mp hm).2]
    · rw [abs_of_nonpos hs]
      rcases le_total 0 b with hb | hb
      · rw [abs_of_nonneg hb]
        linarith [(abs_le.mp hm).1]
      · rw [abs_of_nonpos hb]
        linarith [(abs_le.mp hp).1]
  have ha : |a| ≤ |a + c| + |c| := by simpa using abs_sub (a + c) c
  linarith
