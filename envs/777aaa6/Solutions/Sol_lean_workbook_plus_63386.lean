-- Prove2me | solution 1 for lean_workbook_plus_63386
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:06.978316+00:00
-- url     : https://prove2.me/submissions/ec0a2b9c-b68a-48e6-97e3-5b8c82dd5b78

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas

theorem solution : IsClosed {p : ℝ × ℝ | p.fst * p.snd = 1} := by
  exact isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

#print axioms solution
