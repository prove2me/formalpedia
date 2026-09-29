-- Prove2me | solution 1 for lean_workbook_plus_40320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:19:05.946242+00:00
-- url     : https://prove2.me/submissions/3b554c7d-0104-48ec-afe9-808ef3e62824

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (hab : 1 ≤ a ∧ 1 ≤ b) (h : a + 1 / a ^ 2 ≥ b - 2 / b ^ 2) : a ≥ b / 2 - 1 / b ^ 2 := by
  rcases hab with ⟨ha, hb⟩
  have ha0 : 0 < a := by linarith
  have ha2 : 1 ≤ a^2 := one_le_pow₀ ha
  have hd : 1/a^2 ≤ 1 := (div_le_iff₀ (by positivity : 0 < a^2)).2 (by simpa using ha2)
  simp only [div_eq_mul_inv, one_mul] at h hd ⊢
  linarith
