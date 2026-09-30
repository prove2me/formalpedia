-- Prove2me | solution 1 for lean_workbook_plus_23158
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:13.742474+00:00
-- url     : https://prove2.me/submissions/86529428-60c9-4e04-a68a-79c85d6b847a

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = fun x => if x < 0 then x else f x) : ∀ x < 0, f x = x := by
  intro x hx
  have h := congrFun hf x
  simp only [if_pos hx] at h
  exact h
