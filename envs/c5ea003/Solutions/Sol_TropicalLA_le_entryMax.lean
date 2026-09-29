-- Prove2me | solution 1 for TropicalLA.le_entryMax
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:11:56.673472+00:00
-- url     : https://prove2.me/submissions/eed2c248-6e79-4e14-b1bd-14daa1ab1a58

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} (i j : ι) :
    finPart A i j ≤ entryMax A := by
  show finPart A i j
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun p : ι × ι => finPart A p.1 p.2)
  exact Finset.le_sup' (fun p : ι × ι => finPart A p.1 p.2) (Finset.mem_univ (i, j))
