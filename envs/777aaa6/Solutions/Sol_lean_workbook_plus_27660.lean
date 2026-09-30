-- Prove2me | solution 1 for lean_workbook_plus_27660
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:49:21.982538+00:00
-- url     : https://prove2.me/submissions/57bae450-fdd6-4b57-926e-e20da695495d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution {a b x y : Real} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
    (a * x + b * y) / (a + b) ≥ (a + b) / (a / x + b / y) := by
  have hab : a + b ≠ 0 := by positivity
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hd1 : a / x + b / y ≠ 0 := by positivity
  have hd2 : a * y + b * x ≠ 0 := by positivity
  have hid : (a * x + b * y) / (a + b) - (a + b) / (a / x + b / y) =
      a * b * (x - y) ^ 2 / ((a + b) * (a * y + b * x)) := by
    field_simp
    ring
  have hn : 0 ≤ a * b * (x - y) ^ 2 := by positivity
  have hd : 0 < (a + b) * (a * y + b * x) := by positivity
  have hdiff : 0 ≤ (a * x + b * y) / (a + b) - (a + b) / (a / x + b / y) := by
    rw [hid]
    exact div_nonneg hn hd.le
  linarith

#print axioms solution
