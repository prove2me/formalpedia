-- Prove2me | solution 2 for mme_omega_eq_strassen
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:59:26.919837+00:00
-- url     : https://prove2.me/submissions/21e496bf-3397-4d3f-a0c2-2e0b3abb35f7

import Theorems.Thm_mme_tensorRank_le_strassenRank
import Theorems.Thm_mme_strassenRank_le_tensorRank

open MME

universe u

/-- The decomposition and restriction definitions give the same matrix multiplication exponent. -/
theorem solution {K : Type u} [Field K] :
    matMulExp K = matMulExp_strassen K := by
  have hrank : ∀ {d : ℕ} {V : Fin d → Type u} [∀ i, AddCommGroup (V i)]
      [∀ i, Module K (V i)] (T : PiTensorProduct K V), tensorRank T = strassenRank T :=
    fun T => le_antisymm (mme_tensorRank_le_strassenRank T) (mme_strassenRank_le_tensorRank T)
  simp only [matMulExp, matMulExp_strassen, hrank]


#print axioms solution
