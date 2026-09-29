-- Prove2me | solution 1 for SymplecticMatrix.standardGenerators_mem_sp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T15:47:12.793626+00:00
-- url     : https://prove2.me/submissions/35f542c8-0294-4b99-98a3-ba571621b96e

import Definitions.Def_symplectic_block_generators
import Theorems.Thm_SymplecticMatrix_mem_sp_iff_blocks

open Matrix SymplecticMatrix

theorem solution {l : ℕ} {R : Type*} [CommRing R] (i j : Fin l) :
    (elemX i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R ∧
      (elemT i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R ∧
      (elemS i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R := by
  refine ⟨?_, ?_, ?_⟩
  · rw [elemX, SymplecticMatrix.mem_sp_iff_blocks]
    exact ⟨rfl, by simp, by simp⟩
  · rw [elemT, SymplecticMatrix.mem_sp_iff_blocks]
    exact ⟨by simp, by simp, by simp⟩
  · rw [elemS, SymplecticMatrix.mem_sp_iff_blocks]
    exact ⟨by simp, by simp, by simp⟩
