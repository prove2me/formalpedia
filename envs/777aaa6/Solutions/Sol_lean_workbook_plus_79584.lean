-- Prove2me | solution 1 for lean_workbook_plus_79584
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:50.757271+00:00
-- url     : https://prove2.me/submissions/cb2e749e-42f5-415e-9ffa-07bfb320083e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) :
    6 * a * b + 1 / (a + b) ≤ 65 / 4 + a ^ 2 + b ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have heq : a + b = a * b := by
    field_simp at hab
    linarith
  have hs : 4 ≤ a + b := by
    by_contra hn
    have hp := mul_pos (add_pos ha hb) (show 0 < 4 - (a + b) by linarith)
    nlinarith [sq_nonneg (a - b)]
  have hi : 1 / (a + b) ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ (add_pos ha hb) (by norm_num)).2
    linarith
  nlinarith [sq_nonneg (a + b - 4)]
