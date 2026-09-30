-- Prove2me | solution 1 for lean_workbook_plus_82715
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:12.133528+00:00
-- url     : https://prove2.me/submissions/29782bc9-68fb-46b1-9343-a1cf1d670828

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (f : ℝ → ℝ) (h₁ : ∀ x, f x = a * x ^ 2 + b * x) : ∃ a b, ∀ x, f x = a * x ^ 2 + b * x :=
  ⟨a, b, h₁⟩
