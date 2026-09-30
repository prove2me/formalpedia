-- Prove2me | solution 1 for lean_workbook_plus_75403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:09:21.710715+00:00
-- url     : https://prove2.me/submissions/e0c31de1-1f0d-4e8e-8b6d-9b422c4fc0c7

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h : a ≤ b) :
  ⋂ (n : ℕ), (Set.Icc (a - 1 / n) (b + 1 / n)) = Set.Icc a b := by
  ext x
  simp only [Set.mem_iInter, Set.mem_Icc]
  constructor
  · intro hx
    have h0 := hx 0
    simpa using h0
  · rintro ⟨hax, hxb⟩ n
    have hn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    constructor <;> linarith
