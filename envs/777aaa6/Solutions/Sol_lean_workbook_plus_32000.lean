-- Prove2me | solution 1 for lean_workbook_plus_32000
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:01:57.945546+00:00
-- url     : https://prove2.me/submissions/4ec47c2e-2ad2-48b9-85df-01e8637c2ce3

import Mathlib.Analysis.Complex.Basic

theorem solution : Continuous fun x => Real.sqrt (x ^ 2 + 16) := by
  exact (continuous_id.pow 2 |>.add continuous_const).sqrt

#print axioms solution
