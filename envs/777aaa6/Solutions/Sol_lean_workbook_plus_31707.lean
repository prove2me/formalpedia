-- Prove2me | solution 1 for lean_workbook_plus_31707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:38.920762+00:00
-- url     : https://prove2.me/submissions/881e8171-936e-41e4-82eb-8b7b7a4442ec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ)
  (h₀ : b ≤ max a c)
  (h₁ : b ≥ min a c) :
  a * (b - a) * (b - c) ≤ 0 ↔ a^2 * b + a * b * c ≥ a * b^2 + c * a^2 := by
  intros
  grind
