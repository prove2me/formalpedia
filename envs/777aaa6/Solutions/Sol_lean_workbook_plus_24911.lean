-- Prove2me | solution 1 for lean_workbook_plus_24911
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:45.770499+00:00
-- url     : https://prove2.me/submissions/aca170b4-148e-4ca5-8624-45c4258498cf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : 8 + 2 * (a * b + b * c + c * a) ≥ 12 + a * b * c ↔ 2 * (a * b + b * c + c * a) - a * b * c ≥ 4 := by
  intros
  grind
