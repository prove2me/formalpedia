-- Prove2me | solution 1 for lean_workbook_plus_57944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:54.253468+00:00
-- url     : https://prove2.me/submissions/9fd16d1f-2ec1-461a-a1e2-a31f9af0e247

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution :
  ¬∀ x y z : ℝ, (x > 0 ∧ y > 0 ∧ z > 0 → √(x^2 + y^2 + 2 * z) + √(y^2 + z^2 + 2 * x) + √(z^2 + x^2 + 2 * y) < √3) := by
  intro h
  have hh := h (1 / 3) (1 / 3) (1 / 3) (by norm_num)
  norm_num at hh
  have hlower : (2 : ℝ) / 3 ≤ Real.sqrt ((8 : ℝ) / 9) :=
    (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  norm_num at hlower
  have hupper : Real.sqrt (3 : ℝ) < 2 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith
