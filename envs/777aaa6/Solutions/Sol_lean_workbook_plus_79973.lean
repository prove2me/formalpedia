-- Prove2me | solution 1 for lean_workbook_plus_79973
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:29.007398+00:00
-- url     : https://prove2.me/submissions/7235d233-3681-4707-aa12-783c9e9bfcef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

private theorem bounded_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + (a + b)) ≤ a / (1 + a) + b / (1 + b) := by
  have h1 : 1 + a ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1 + b ≠ 0 := ne_of_gt (by positivity)
  have h3 : 1 + (a + b) ≠ 0 := ne_of_gt (by positivity)
  have hid : a / (1 + a) + b / (1 + b) - (a + b) / (1 + (a + b)) =
      a * b * (2 + a + b) / ((1 + a) * (1 + b) * (1 + (a + b))) := by
    field_simp
    ring
  have hs : 0 ≤ a * b * (2 + a + b) /
      ((1 + a) * (1 + b) * (1 + (a + b))) := by positivity
  linarith

theorem solution (x y : ℝ) :
    |x + y| / (1 + |x + y|) ≤ |x| / (1 + |x|) + |y| / (1 + |y|) := by
  have hm : |x + y| / (1 + |x + y|) ≤
      (|x| + |y|) / (1 + (|x| + |y|)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [abs_add_le x y]
  exact hm.trans (bounded_add |x| |y| (abs_nonneg x) (abs_nonneg y))
