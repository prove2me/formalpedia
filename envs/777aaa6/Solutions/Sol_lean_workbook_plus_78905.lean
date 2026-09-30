-- Prove2me | solution 1 for lean_workbook_plus_78905
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:53.94669+00:00
-- url     : https://prove2.me/submissions/ebe52fc2-47b4-41c0-847b-c3a98bf5a93d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (x y : ℤ) :
    x^2 - y^2 = (x + y) * (x - y) ∧
    x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) ∧
    x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by
  constructor
  · ring
  constructor <;> ring
