-- Prove2me | solution 1 for TropicalLA.IsTropEigen.le_of
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:44:00.430291+00:00
-- url     : https://prove2.me/submissions/cc2cb2f5-1b1b-4a1a-ae6e-04207bd5423c

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (h : IsTropEigen A lam v) (i j : ι) : A i j + v j ≤ lam + v i := by
  have hi : Finset.univ.sup' Finset.univ_nonempty (fun k => A i k + v k) = lam + v i := h i
  rw [← hi]
  exact Finset.le_sup' (fun k => A i k + v k) (Finset.mem_univ j)
