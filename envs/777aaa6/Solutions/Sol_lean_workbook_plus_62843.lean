-- Prove2me | solution 1 for lean_workbook_plus_62843
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:42.070367+00:00
-- url     : https://prove2.me/submissions/233f0637-d66d-4ae8-bcc4-101189864ac6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℝ) (h : ∀ ε > 0, a + ε > 0) : a ≥ 0 := by
  by_contra ha
  have hneg : a < 0 := lt_of_not_ge ha
  have hbad := h (-a) (neg_pos.mpr hneg)
  linarith

#print axioms solution
