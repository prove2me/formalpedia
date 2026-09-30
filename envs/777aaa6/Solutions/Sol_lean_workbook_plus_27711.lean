-- Prove2me | solution 1 for lean_workbook_plus_27711
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:57:23.435137+00:00
-- url     : https://prove2.me/submissions/e9bf10a1-96b7-4d33-9ffa-ad1d9bc4a772

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem domain_classification (y : Real) :
    1 / (1 + y ^ 2) ≤ (27 / 50) * (2 - y) ↔ y ≤ 4 / 3 := by
  have hd0 : 1 + y ^ 2 ≠ 0 := by positivity
  have hd : 0 < 50 * (1 + y ^ 2) := by positivity
  have hid : (27 / 50) * (2 - y) - 1 / (1 + y ^ 2) =
      (3 * y - 1) ^ 2 * (4 - 3 * y) / (50 * (1 + y ^ 2)) := by
    field_simp
    ring
  constructor
  · intro h
    by_contra hy
    have hy' : 4 / 3 < y := lt_of_not_ge hy
    have hs : 0 < (3 * y - 1) ^ 2 := pow_pos (by linarith) _
    have hn : (3 * y - 1) ^ 2 * (4 - 3 * y) < 0 :=
      mul_neg_of_pos_of_neg hs (by linarith)
    have hneg := div_neg_of_neg_of_pos hn hd
    rw [← hid] at hneg
    linarith
  · intro hy
    have hs : 0 ≤ 4 - 3 * y := by linarith
    have hn : 0 ≤ (3 * y - 1) ^ 2 * (4 - 3 * y) :=
      mul_nonneg (sq_nonneg _) hs
    have hdiff := div_nonneg hn hd.le
    rw [← hid] at hdiff
    linarith

theorem solution : ¬ (∀ y : Real, 1 / (1 + y ^ 2) ≤ (27 / 50) * (2 - y)) := by
  intro h
  have hc : (2 : Real) ≤ 4 / 3 := (domain_classification 2).mp (h 2)
  norm_num at hc

#print axioms solution
