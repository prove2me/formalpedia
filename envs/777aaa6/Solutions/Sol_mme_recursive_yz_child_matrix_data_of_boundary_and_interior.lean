-- Prove2me | solution 1 for mme_recursive_yz_child_matrix_data_of_boundary_and_interior
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T13:45:31.92946+00:00
-- url     : https://prove2.me/submissions/2b0b56e4-3ea2-44fe-9b52-ddc1616344a8

import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
open BigOperators MME MME.TensorObj MME.RecursiveYZ.Certificate
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (P : A.ChildPlan K) :
    ∃ M : A.ChildMM K, M.dimA = P.dimA ∧ M.dimB = P.dimB ∧ M.dimC = P.dimC := by
  have hex (j : Fin A.childCells) :
      Restrict (MMObj K (P.a j) (P.b j) (P.c j)) (A.childTensor K j) := by
    rcases P.cases j with h | h
    · rcases h with ⟨z,B,hshape,hmu,ha,hb,hc⟩
      rw [ha,hb,hc]
      have ht : A.childTensor K j = B.tensor K z := by
        simp only [Stage.childTensor, MME.RecursiveYZ.Boundary.Profile.tensor]
        simp_rw [hshape, hmu]
      rw [ht]
      exact mme_recursive_yz_boundary_actual_matrix_extraction B z
    · exact h.2
  exact ⟨{a := P.a, b := P.b, c := P.c, extract := hex}, rfl, rfl, rfl⟩
