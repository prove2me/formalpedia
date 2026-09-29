-- Prove2me | Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
-- name    : mme_primary_hash_family_sharedZ_star_grading_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:07:08.540464+00:00
-- url     : https://prove2.me/theorems/6e30ee0f-73bf-4bee-9d71-3d807af2091b
-- title:
--   One-H-one grading and component blocks of every shared-Z star
-- statement:
--   Each outer fiber of a primary hash family forms a shared-third-mode C-tensor star. Its canonical basis grading is supported only on the $H$ addresses $(h,h,*)$. For every inner index $h$, the corresponding graded block is isomorphic to the exact coupled graded-address component selected by $(a,h)$. Thus the star has the precise $\langle1,H,1\rangle$ block pattern independently of any later matrix-multiplication dimension calculation.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME

universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

open CoupledCTensorPackaging

theorem mme_primary_hash_family_sharedZ_star_grading_components
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∀ a : Fin A,
      (∀ σ : Fin 3 → Fin (H + 1),
        σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
          (starGrading grading family a).blockTensor σ = 0) ∧
      ∀ h : Fin H,
        TensorObj.Isomorphic
          (componentObj grading family a h)
          ((starGrading grading family a).blockSubtensor
            (cTensorOneHOneAddress H h)) := by
  sorry
