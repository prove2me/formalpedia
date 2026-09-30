-- Prove2me | solution 1 for lean_workbook_plus_25053
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:14:47.78678+00:00
-- url     : https://prove2.me/submissions/abd5bce6-a6b1-42c2-9946-ba800a9f034f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

lemma valid_domain (x : ℝ) :
    (1 + x) * (x + 3) * (x + 9) * (x + 11) * (x + 14) ≥ 14400 * x ↔
    -21 ≤ x := by
  have hq : 0 < x ^ 2 + 19 * x + 198 := by nlinarith [sq_nonneg (2 * x + 19)]
  have hid :
      (1 + x) * (x + 3) * (x + 9) * (x + 11) * (x + 14) - 14400 * x =
      (x - 1) ^ 2 * (x + 21) * (x ^ 2 + 19 * x + 198) := by ring
  constructor
  · intro h
    by_contra he
    have hx21 : x + 21 < 0 := by linarith
    have hs : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (by intro hz; linarith)
    have hn := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hx21) hq
    linarith
  · intro h
    have hn := mul_nonneg
      (mul_nonneg (sq_nonneg (x - 1)) (show 0 ≤ x + 21 by linarith)) (le_of_lt hq)
    linarith

theorem solution : ¬ (∀ x : ℝ,
    (1 + x) * (x + 3) * (x + 9) * (x + 11) * (x + 14) ≥ 14400 * x) := by
  intro h
  have hx := (valid_domain (-22)).1 (h (-22))
  norm_num at hx
