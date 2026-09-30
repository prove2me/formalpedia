-- Prove2me | solution 1 for lean_workbook_plus_6476
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:39.72784+00:00
-- url     : https://prove2.me/submissions/16ebf103-956a-47b0-8b8f-530ac6f2fbf3

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : (2014^n - n^2014 ≡ 0 [ZMOD 11]) → n >= 1 := by
  intro h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    norm_num [Int.ModEq] at h
  · exact hn
