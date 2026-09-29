-- Prove2me | solution 1 for TropicalLA.isTropEigen_of
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T09:06:09.490658+00:00
-- url     : https://prove2.me/submissions/57c8aabf-acb2-463b-8ac6-3591ab88ab1a

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ) (lam : ℝ) (v : ι → ℝ)
    (hup : ∀ i j, A i j + v j ≤ lam + v i) (htight : ∀ i, ∃ j, A i j + v j = lam + v i) :
    IsTropEigen A lam v := by
  intro i
  show Finset.univ.sup' Finset.univ_nonempty (fun k => A i k + v k) = lam + v i
  refine le_antisymm (Finset.sup'_le _ _ fun j _ => hup i j) ?_
  obtain ⟨j, hj⟩ := htight i
  rw [← hj]
  exact Finset.le_sup' (fun k => A i k + v k) (Finset.mem_univ j)
