-- Prove2me | solution 1 for lean_workbook_plus_27630
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:49:37.648045+00:00
-- url     : https://prove2.me/submissions/8fc04284-ea00-4ee0-a6e7-461fe74d347f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : Real) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + 1 / 2) * (b + c + 1 / 2) * (c + a + 1 / 2) ≥
      (2 * a + 1 / 2) * (2 * b + 1 / 2) * (2 * c + 1 / 2) := by
  have hid : (a + b + 1 / 2) * (b + c + 1 / 2) * (c + a + 1 / 2) -
      (2 * a + 1 / 2) * (2 * b + 1 / 2) * (2 * c + 1 / 2) =
      (a + 1 / 4) * (b - c) ^ 2 + (b + 1 / 4) * (c - a) ^ 2 +
        (c + 1 / 4) * (a - b) ^ 2 := by
    ring
  have hn : 0 ≤ (a + 1 / 4) * (b - c) ^ 2 + (b + 1 / 4) * (c - a) ^ 2 +
      (c + 1 / 4) * (a - b) ^ 2 := by positivity
  linarith only [hid, hn]

#print axioms solution
