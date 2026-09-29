-- Prove2me | solution 1 for lean_workbook_plus_25115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:08.656031+00:00
-- url     : https://prove2.me/submissions/4b1929d2-72bf-48f8-ad49-eaace9e2a420

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ x : ℝ, x ≠ 0 → 1 + 1 / (2 * x ^ 2) ≥ Real.sqrt ((1 + x ^ 2) / x ^ 2) := by
  intro x hx
  have hn : 0 ≤ 1 / x ^ 2 := by positivity
  have h := Real.sqrt_one_add_le (x := 1 / x ^ 2) (by linarith)
  have hr : (1 + x ^ 2) / x ^ 2 = 1 + 1 / x ^ 2 := by
    field_simp [hx]
    <;> ring
  have he : 1 + 1 / x ^ 2 / 2 = 1 + 1 / (2 * x ^ 2) := by ring
  change Real.sqrt ((1 + x ^ 2) / x ^ 2) ≤ 1 + 1 / (2 * x ^ 2)
  rw [hr, ← he]
  exact h
