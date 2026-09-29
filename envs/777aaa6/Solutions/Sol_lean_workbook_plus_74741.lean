-- Prove2me | solution 1 for lean_workbook_plus_74741
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:05.299655+00:00
-- url     : https://prove2.me/submissions/d1842c86-e3c0-4f5f-8488-df56c2454c90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ a b c : ℤ, a^3 + b^3 = c^3 ∧ (a = 0 ∧ b = 0 ∧ c = 0) ∨ (∃ k : ℤ, a = k ∧ b = -k ∧ c = 0) := by
  intros
  grind
