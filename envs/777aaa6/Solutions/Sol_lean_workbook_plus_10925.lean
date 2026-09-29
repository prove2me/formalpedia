-- Prove2me | solution 1 for lean_workbook_plus_10925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:25.68794+00:00
-- url     : https://prove2.me/submissions/77c7a31c-4451-4940-8f13-1c49da63fb23

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℕ → ℚ) (f0 : f 0 = 1 / 2) (f_rec : ∀ n, n > 0 → f n = if n % 2 = 0 then f (n - 1) else 1 - f (n - 1)) : f 2007 = 1 / 2 := by
  have hall : ∀ n, f n=1/2 := by
    intro n
    induction n with
    | zero => exact f0
    | succ n ih =>
      rw [f_rec (n+1) (by omega)]
      split_ifs <;> simp only [Nat.add_sub_cancel,ih] <;> norm_num
  exact hall 2007
