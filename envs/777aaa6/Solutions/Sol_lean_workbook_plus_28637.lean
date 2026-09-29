-- Prove2me | solution 1 for lean_workbook_plus_28637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:28.235427+00:00
-- url     : https://prove2.me/submissions/571207a1-b93e-4c55-99ab-6b97e896fbf7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c d e : ℝ} (h1 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e) : d + e ≥ c + e ∧ c + e ≥ d + b ∧ d + b ≥ a + c ∧ a + c ≥ a + b ∧ a + b ≥ 0 := by
  intros
  grind
