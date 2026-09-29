-- Prove2me | solution 1 for lean_workbook_plus_77671
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:40.835104+00:00
-- url     : https://prove2.me/submissions/7ae03422-cf11-47c2-b8ec-0fcfc39da83b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a : ℝ) (f g : ℝ → ℝ) (hf: f x = a - x) (hg: g x = a - x) : f x = g x := by
  (intros; simp_all)
