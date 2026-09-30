-- Prove2me | solution 1 for lean_workbook_plus_52505
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:52.886234+00:00
-- url     : https://prove2.me/submissions/699053a7-f8de-47a2-a875-a8968e16098c

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x) : ∃ a, ∀ x, f x = a * x :=
  ⟨a, h⟩
