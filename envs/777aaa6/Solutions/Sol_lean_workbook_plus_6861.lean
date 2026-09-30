-- Prove2me | solution 1 for lean_workbook_plus_6861
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:24.326253+00:00
-- url     : https://prove2.me/submissions/9f3930cb-c2a5-4eb6-8ef8-b0853671122c

import Mathlib.Analysis.Complex.Basic

theorem solution (k u v : ℕ) (h₁ : 2 * k + 1 = u ^ 2) (h₂ : 3 * k + 1 = v ^ 2) : ∃ k u v : ℕ, 2 * k + 1 = u ^ 2 ∧ 3 * k + 1 = v ^ 2 := by
  exact ⟨0, 1, 1, by norm_num, by norm_num⟩
