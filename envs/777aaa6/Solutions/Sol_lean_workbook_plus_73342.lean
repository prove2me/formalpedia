-- Prove2me | solution 1 for lean_workbook_plus_73342
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:43.317276+00:00
-- url     : https://prove2.me/submissions/d670adfa-d7cc-480e-923a-07a5c51dd17a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    (x + y) * (y + z) * (z + t) * (t + x) ≥
      (x + y + z + t) * (x * y * z + y * z * t + z * t * x + t * x * y) := by
  nlinarith [sq_nonneg (x * z - y * t)]
