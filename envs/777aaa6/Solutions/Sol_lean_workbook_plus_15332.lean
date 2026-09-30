-- Prove2me | solution 1 for lean_workbook_plus_15332
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:19.589741+00:00
-- url     : https://prove2.me/submissions/cd79ecd2-f963-4c16-b984-0ba244acff90

import Mathlib.Analysis.Complex.Basic

theorem solution (m n : ℤ) (h : m.gcd n = 1) : ∃ N : ℕ, ∀ n : ℤ, n >= N → ∃ a b : ℤ, n = m * a + n * b := by
  exact ⟨0, fun n _ => ⟨0, 1, by ring⟩⟩
