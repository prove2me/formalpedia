-- Prove2me | solution 1 for lean_workbook_plus_42749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:22.00029+00:00
-- url     : https://prove2.me/submissions/d0915259-76e8-4db4-9c58-74f9b8fef322

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : (a^2 + 1) * (b^2 + 1) ≥ a * (b^2 + 1) + b * (a^2 + 1) ↔ a / (a^2 + 1) + b / (b^2 + 1) ≤ 1 := by
  intros
  field_simp at * <;> ring
