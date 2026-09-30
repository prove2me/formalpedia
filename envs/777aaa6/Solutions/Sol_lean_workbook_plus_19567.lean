-- Prove2me | solution 1 for lean_workbook_plus_19567
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:14.753653+00:00
-- url     : https://prove2.me/submissions/896e7bd9-317e-412a-8399-eac9632d5d79

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 2 < n) : 3^n > 3*n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge 2 k with hk | hk
    · have := ih hk
      rw [pow_succ]
      omega
    · have : k = 2 := by omega
      subst this
      norm_num
