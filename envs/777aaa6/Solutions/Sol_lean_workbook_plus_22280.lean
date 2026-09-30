-- Prove2me | solution 1 for lean_workbook_plus_22280
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:20.5453+00:00
-- url     : https://prove2.me/submissions/f300f665-fc54-43cb-92dc-23d96e18b1ce

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

theorem solution (n k m a b c : ℕ)
  (h₀ : 0 < n ∧ 0 < k ∧ 0 < m ∧ 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : n^k + n^m = n^a + n^b + n^c)
  (h₂ : k ≤ a ∧ m ≤ b ∧ c ≤ k)
  (h₃ : n ≤ 2) :
  n = 2 := by
  obtain ⟨hn, -⟩ := h₀
  interval_cases n
  · simp at h₁
  · rfl
