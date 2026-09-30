-- Prove2me | solution 1 for lean_workbook_plus_78624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:55.877104+00:00
-- url     : https://prove2.me/submissions/c1910d45-5a04-48a1-a070-fd712942c794

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) :
    (abs (a + b) : ℝ) / (1 + abs (a + b)) ≤
      abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have ha : 0 < 1 + |a| := by positivity
  have hb : 0 < 1 + |b| := by positivity
  have hs : 0 < 1 + |a + b| := by positivity
  have hab : 0 < 1 + |a| + |b| := by positivity
  calc
    |a + b| / (1 + |a + b|) ≤ (|a| + |b|) / (1 + |a| + |b|) := by
      apply (div_le_div_iff₀ hs hab).2
      nlinarith [abs_add_le a b]
    _ = |a| / (1 + |a| + |b|) + |b| / (1 + |a| + |b|) := by
      rw [add_div]
    _ ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
      exact add_le_add
        (div_le_div_of_nonneg_left (abs_nonneg a) ha (by linarith [abs_nonneg b]))
        (div_le_div_of_nonneg_left (abs_nonneg b) hb (by linarith [abs_nonneg a]))

#print axioms solution
