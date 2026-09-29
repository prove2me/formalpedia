-- Prove2me | solution 1 for lean_workbook_plus_24593
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:30.637016+00:00
-- url     : https://prove2.me/submissions/6eb148ff-b03e-497d-babe-ec47fa84b8cd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z t : ℝ)
  (h₀ : x = 2 * t + 1)
  (h₁ : y = 2 * t - 1)
  (h₂ : z = 3 * t + 2)
  (h₃ : 0 < t) :
  x * y + y * z + z * x ≥ 16 * t^2 + 8 * t - 1 := by
  intros
  nlinarith
