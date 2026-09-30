-- Prove2me | solution 1 for lean_workbook_plus_77909
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:01:01.333602+00:00
-- url     : https://prove2.me/submissions/76b9e347-9b4f-4e83-b0a5-7c2834d4f0d9

import Mathlib.Analysis.Complex.Basic

theorem solution : Continuous (fun x : ℝ => x ^ 3) := by
  exact continuous_id.pow 3

#print axioms solution
