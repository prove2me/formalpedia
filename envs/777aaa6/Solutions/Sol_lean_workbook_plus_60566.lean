-- Prove2me | solution 1 for lean_workbook_plus_60566
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:24:28.58071+00:00
-- url     : https://prove2.me/submissions/fd1eeda1-f54f-430f-ace7-abbb6f52a12b

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℕ → ℕ) (n₀ : ℕ) (h : ∀ n ≥ n₀, a n = a n₀) : ∃ n₀, ∀ n ≥ n₀, a n = a n₀ :=
  ⟨n₀, h⟩
