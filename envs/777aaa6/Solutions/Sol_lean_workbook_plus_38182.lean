-- Prove2me | solution 1 for lean_workbook_plus_38182
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:31.733607+00:00
-- url     : https://prove2.me/submissions/e4f2b29e-0cfe-4bd3-9254-8bb2009d513a

import Mathlib.Analysis.Complex.Basic

theorem solution : ContinuousAt (fun x : ℝ => x^2) 0 := by
  fun_prop
