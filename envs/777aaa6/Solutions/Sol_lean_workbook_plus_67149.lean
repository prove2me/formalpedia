-- Prove2me | solution 1 for lean_workbook_plus_67149
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:39:49.406794+00:00
-- url     : https://prove2.me/submissions/36b70dc6-6677-490c-97ad-b1c093a10799

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas

theorem solution (u v : ℝ) (huv : u < v) : IsConnected (Set.Icc u v) := by
  exact isConnected_Icc huv.le

#print axioms solution
