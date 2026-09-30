-- Prove2me | solution 1 for lean_workbook_plus_65859
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:58.177762+00:00
-- url     : https://prove2.me/submissions/009302e2-c558-411f-9d22-2b63179cb645

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas

theorem solution : IsOpen {p : ℝ × ℝ | p.fst < 1 ∧ p.snd > 1} := by
  exact (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)

#print axioms solution
