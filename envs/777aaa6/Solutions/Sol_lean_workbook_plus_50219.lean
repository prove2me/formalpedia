-- Prove2me | solution 1 for lean_workbook_plus_50219
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:33.579729+00:00
-- url     : https://prove2.me/submissions/c15d066d-2190-4e7c-bf49-125c41be89e8

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h : ∀ ε > 0, |a - b| < ε) : a = b := by
  by_contra hab
  have hp : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  exact (lt_irrefl |a - b|) (h |a - b| hp)

#print axioms solution
