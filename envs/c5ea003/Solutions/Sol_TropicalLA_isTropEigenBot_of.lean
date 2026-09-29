-- Prove2me | solution 1 for TropicalLA.isTropEigenBot_of
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:41:49.151926+00:00
-- url     : https://prove2.me/submissions/366f7b47-dca7-4b65-917a-dc2e67840442

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ} {v : ι → ℝ}
    (hup : ∀ i j, A i j + (v j : WithBot ℝ) ≤ ((lam + v i : ℝ) : WithBot ℝ))
    (ht : ∀ i, ∃ j, A i j + (v j : WithBot ℝ) = ((lam + v i : ℝ) : WithBot ℝ)) :
    IsTropEigenBot A lam v := by
  intro i
  show univ.sup (fun j => A i j + (v j : WithBot ℝ)) = ((lam + v i : ℝ) : WithBot ℝ)
  apply le_antisymm
  · exact Finset.sup_le fun j _ => hup i j
  · obtain ⟨j, hj⟩ := ht i
    rw [← hj]
    exact Finset.le_sup (f := fun j => A i j + (v j : WithBot ℝ)) (mem_univ j)
