-- Prove2me | solution 1 for lean_workbook_plus_45291
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:06.972164+00:00
-- url     : https://prove2.me/submissions/54903616-6b04-42dd-b4d3-ca019d968c7e

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ ({ (a,b) : ℕ × ℕ | a^2 - 2*b^4 = 1} = {(1,1), (239,13)}) := by
  intro h
  have hmem : ((1, 0) : ℕ × ℕ) ∈ { (a,b) : ℕ × ℕ | a^2 - 2*b^4 = 1} := by
    simp
  rw [h] at hmem
  simp at hmem
