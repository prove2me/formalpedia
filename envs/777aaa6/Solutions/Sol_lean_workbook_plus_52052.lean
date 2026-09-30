-- Prove2me | solution 1 for lean_workbook_plus_52052
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:04.898932+00:00
-- url     : https://prove2.me/submissions/d0fa9b76-6a97-4412-ab18-c67281c85933

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (p q r : ℂ)
    (hp : p ^ 3 - 9 * p ^ 2 + 8 * p + 2 = 0)
    (hq : q ^ 3 - 9 * q ^ 2 + 8 * q + 2 = 0)
    (hr : r ^ 3 - 9 * r ^ 2 + 8 * r + 2 = 0) :
    p * (p - 1) * (p - 8) + q * (q - 1) * (q - 8) + r * (r - 1) * (r - 8) = -6 := by
  linear_combination hp + hq + hr

#print axioms solution
