-- Prove2me | solution 1 for lean_workbook_plus_17522
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:41:24.978049+00:00
-- url     : https://prove2.me/submissions/715b2810-9421-42f8-8a36-31187f3e9981

import Mathlib.Analysis.Complex.Basic

theorem solution (g : ℝ → ℝ) (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = 0) :
    ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
  continuousOn_const.congr hg

#print axioms solution
