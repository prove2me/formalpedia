-- Prove2me | solution 1 for TropicalLA.coe_finPart
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:39:08.975021+00:00
-- url     : https://prove2.me/submissions/0a630aca-61a8-4960-9c0a-9d48334277f7

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} {A : Matrix ι ι (WithBot ℝ)} {i j : ι}
    (h : A i j ≠ ⊥) : ((finPart A i j : ℝ) : WithBot ℝ) = A i j := by
  obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp h
  show (((A i j).unbotD 0 : ℝ) : WithBot ℝ) = A i j
  rw [← hr]
  simp
