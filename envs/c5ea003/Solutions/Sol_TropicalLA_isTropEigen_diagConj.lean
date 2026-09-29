-- Prove2me | solution 1 for TropicalLA.isTropEigen_diagConj
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:34:58.539819+00:00
-- url     : https://prove2.me/submissions/aac92b67-31ce-42cb-a1f5-7a62f8f83839

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalSpectralInvariants
open TropicalLA Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (d : ι → ℝ) (h : IsTropEigen A lam v) :
    IsTropEigen (diagConj A d) lam (fun i => v i + d i) := by
  intro i
  have hi := h i
  unfold tmulVec at hi ⊢
  simp only [diagConj, Matrix.of_apply]
  -- each term is `d i + (A i j + v j)`: the conjugation telescopes
  apply le_antisymm
  · refine sup'_le _ _ fun j _ => ?_
    have hle := le_sup' (fun j => A i j + v j) (mem_univ j)
    linarith
  · obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' univ_nonempty (fun j => A i j + v j)
    have hle := le_sup' (fun j => d i + A i j - d j + (v j + d j)) (mem_univ j)
    linarith
