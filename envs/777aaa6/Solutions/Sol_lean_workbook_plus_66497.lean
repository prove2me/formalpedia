-- Prove2me | solution 1 for lean_workbook_plus_66497
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:17:53.786226+00:00
-- url     : https://prove2.me/submissions/dc1a4f6a-3224-4379-a41c-d81838071c17

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a : ℝ) (h : ∀ n : ℕ, 0 ≤ a ∧ a ≤ 1 / n) : a = 0 := by
  by_contra hne
  have ha : 0 < a := by
    have hnonneg := (h 1).1
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt ha
  have hb : a ≤ 1 / ((k:ℝ)+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (h (k+1)).2
  linarith
