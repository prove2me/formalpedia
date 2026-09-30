-- Prove2me | solution 1 for lean_workbook_plus_30231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:35.221717+00:00
-- url     : https://prove2.me/submissions/b6278f17-c20d-4252-b165-41e049951a8a

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ n ≥ 2, (5 : ℝ)^n + 9 < 6^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 5) k]
