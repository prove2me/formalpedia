-- Prove2me | solution 1 for lean_workbook_plus_28973
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:10.503945+00:00
-- url     : https://prove2.me/submissions/3a2416e6-dae5-4513-9878-2c0d77543eca

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → NNReal) (d : ℝ) (hd : d < 1) (h : ∀ n, (x n)^(1/n) = d) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x n < ε := by
  exfalso
  have h0 := h 0
  simp at h0
  linarith
