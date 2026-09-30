-- Prove2me | solution 1 for lean_workbook_plus_5654
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:17:22.594065+00:00
-- url     : https://prove2.me/submissions/a365d1fa-4f84-4e35-8698-a67b261593e1

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = fun x => 1/x + 2005) : f 1 = 2006 := by
  subst hf
  norm_num
