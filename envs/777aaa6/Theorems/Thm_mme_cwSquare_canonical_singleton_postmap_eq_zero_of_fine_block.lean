-- Prove2me | Theorems.Thm_mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
-- name    : mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:07:32.165349+00:00
-- url     : https://prove2.me/theorems/b8dea1f8-506f-46f8-80f9-2125d8d8c112
-- title:
--   A zero fine CW-square block annihilates its canonical singleton
-- statement:
--   Choose one canonical basis pair in each of the three modes of the square of the Coppersmith--Winograd tensor. These pairs determine a fine split grading block by retaining their two coordinate grades separately. If that fine block is zero, then projecting onto the three chosen singleton basis pairs yields the zero tensor, even after arbitrary mode-wise linear postprocessing.
-- source:
--   Canonical fine support of the Coppersmith--Winograd square; standard homogeneous-basis block factorization.

import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_dwz_basis_label_projection

open MME Module PiTensorProduct TensorProduct
open MME.DWZStep1Support

universe u

set_option autoImplicit false

theorem mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
    {K : Type u} [Field K] (q : ℕ)
    (selected : ∀ _ : Fin 3, Fin (q + 2) × Fin (q + 2))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) →ₗ[K] W i)
    (hzero : (cwSquareFineSplitGrading K q).blockTensor
      (fun i ↦ fineSplitGrade
        (cwSquareCoordGrade q (selected i).1)
        (cwSquareCoordGrade q (selected i).2)) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (cwSquareCanonicalBasis K q i) id {selected i}))
        (TensorObj.kron (CWObj K q) (CWObj K q)).t = 0 := by
  sorry
