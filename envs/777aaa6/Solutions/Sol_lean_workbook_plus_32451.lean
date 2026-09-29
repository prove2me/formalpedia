-- Prove2me | solution 1 for lean_workbook_plus_32451
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:20:24.25102+00:00
-- url     : https://prove2.me/submissions/5d8416d2-fdba-4dc8-8039-a05222e9846c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x y z : ℤ} : 5 * (x - y) * (y - z) * (z - x) ∣ (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 := by
  refine ⟨x^2+y^2+z^2-x*y-y*z-z*x, ?_⟩
  ring
