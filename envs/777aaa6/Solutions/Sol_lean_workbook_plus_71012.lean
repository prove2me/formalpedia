-- Prove2me | solution 1 for lean_workbook_plus_71012
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:38:50.445743+00:00
-- url     : https://prove2.me/submissions/290e265d-6f45-420f-9a15-b6d5dbe85bea

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem rational_gap_identity (x : ℝ) (hx : x + 4 ≠ 0) :
    4 / 5 - (x / (x ^ 2 + 4) + 3 / (x + 4)) =
      4 * (x - 1) ^ 2 * (x + 1) / (5 * (x ^ 2 + 4) * (x + 4)) := by
  have hq : x ^ 2 + 4 ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp [hx, hq]
  ring

theorem rational_validity (x : ℝ) :
    (x / (x ^ 2 + 4) + 3 / (x + 4) ≤ 4 / 5) ↔ x ≤ -4 ∨ -1 ≤ x := by
  by_cases hpole : x = -4
  · subst x
    norm_num
  have hx : x + 4 ≠ 0 := by intro h; apply hpole; linarith
  have hq : 0 < x ^ 2 + 4 := by nlinarith [sq_nonneg x]
  rw [← sub_nonneg, rational_gap_identity x hx]
  by_cases hleft : x < -4
  · have hd : 5 * (x ^ 2 + 4) * (x + 4) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) hq) (by linarith)
    have hn : 4 * (x - 1) ^ 2 * (x + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (sq_nonneg _))
        (by linarith)
    constructor
    · intro _
      exact Or.inl hleft.le
    · intro _
      exact div_nonneg_of_nonpos hn hd.le
  · have hx4 : -4 < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hpole)
    have hd : 0 < 5 * (x ^ 2 + 4) * (x + 4) :=
      mul_pos (mul_pos (by norm_num) hq) (by linarith)
    rw [le_div_iff₀ hd, zero_mul]
    constructor
    · intro hn
      right
      by_contra hright
      have hs : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (by intro h; linarith)
      have hneg : 4 * (x - 1) ^ 2 * (x + 1) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (by norm_num) hs) (by linarith)
      linarith
    · rintro (hbad | hright)
      · linarith
      · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)

theorem solution : ¬ (∀ x : ℝ, x / (x ^ 2 + 4) + 3 / (x + 4) ≤ 4 / 5) := by
  intro h
  have hc := (rational_validity (-2)).mp (h (-2))
  norm_num at hc
