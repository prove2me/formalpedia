-- Prove2me | solution 1 for lean_workbook_plus_30241
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:15:02.343823+00:00
-- url     : https://prove2.me/submissions/d10aacc5-c3ff-4c6e-82b6-4534bdd48121

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (Q : ℝ → ℝ) (P : ℝ → ℝ) (h₁ : P = fun x => x * (x - 1) * (x - 2) * Q x + a * x ^ 2 + b * x + c) : ∃ a b c : ℝ, ∀ x : ℝ, P x = x * (x - 1) * (x - 2) * Q x + a * x ^ 2 + b * x + c := by
  exact ⟨a, b, c, fun x => by rw [h₁]⟩
