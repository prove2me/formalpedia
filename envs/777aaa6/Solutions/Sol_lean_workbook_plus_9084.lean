-- Prove2me | solution 1 for lean_workbook_plus_9084
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:27.054332+00:00
-- url     : https://prove2.me/submissions/c0a8c150-81bd-4c45-868e-89fa357c2dfd

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b^2 + c^2 = 1) : (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 50 / 27 ∧ (a = 1 / 3 ∧ b = 0 ∧ c = Real.sqrt (2 / 3) ∨ a = 1 / 3 ∧ b = Real.sqrt (2 / 3) ∧ c = 0) ↔ a = 1 / 3 ∧ b = 0 ∧ c = Real.sqrt (2 / 3) ∨ a = 1 / 3 ∧ b = Real.sqrt (2 / 3) ∧ c = 0 := by
  constructor
  · rintro ⟨_, hq⟩
    exact hq
  · intro hq
    refine ⟨?_, hq⟩
    have hs : Real.sqrt (2 / 3) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
    rcases hq with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rw [hs] <;> norm_num
