-- Prove2me | solution 1 for TropicalLA.entryMin_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:04:53.171621+00:00
-- url     : https://prove2.me/submissions/11f3abd0-629d-4b0c-be4a-63238dba6418

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} (i j : ι) :
    entryMin A ≤ finPart A i j := by
  show Finset.univ.inf' Finset.univ_nonempty (fun p : ι × ι => finPart A p.1 p.2)
      ≤ finPart A i j
  exact Finset.inf'_le _ (Finset.mem_univ (i, j))
