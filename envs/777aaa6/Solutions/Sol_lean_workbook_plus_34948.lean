-- Prove2me | solution 1 for lean_workbook_plus_34948
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:50.012357+00:00
-- url     : https://prove2.me/submissions/47f0209e-d504-484f-9eb3-7a6edec30edb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ)
  (h₀ : x * z = 0.55)
  (h₁ : (1 - y) * x = 0.34)
  (h₂ : x * (1 - y) * (1 - z) = 0.15) :
  x = 187 / 190 ∧ y = 36 / 55 ∧ z = 19 / 34 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
