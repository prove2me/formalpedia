-- Prove2me | Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso
-- name    : mme_TypeGrading_kron_blockSubtensor_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:21:50.751855+00:00
-- url     : https://prove2.me/theorems/a148415d-3691-4707-8b15-d1e8d19f6e71
-- title:
--   Paired Kronecker-grading blocks are Kronecker products of factor blocks
-- statement:
--   Let $X$ and $Y$ carry finite internal type gradings, and choose one grading class in every mode of each tensor. The block of the product grading indexed by the resulting pair of class addresses is tensor-isomorphic to the Kronecker product of the two chosen factor blocks. In symbols,
--
--   $$
--   (X \otimes Y)_{(\sigma_X,\sigma_Y)} \cong X_{\sigma_X} \otimes Y_{\sigma_Y}.
--   $$
--
--   This identifies the abstract paired block spaces and their tensor element simultaneously. It is the structural step used to read matrix-multiplication dimensions of blocks in iterated and cyclic Kronecker products.
-- source:
--   Standard tensor-product direct-sum decomposition; used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 264 and 270--272, https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_TypeGrading_kron

open MME TensorProduct PiTensorProduct
open MME.TensorObj.TypeGrading

universe u

theorem mme_TypeGrading_kron_blockSubtensor_iso
    {K : Type u} [Field K] {d tx ty : ℕ}
    {X Y : TensorObj K d}
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (sx : Fin d → Fin tx) (sy : Fin d → Fin ty) :
    TensorObj.Isomorphic
      (TensorObj.kron (GX.blockSubtensor sx) (GY.blockSubtensor sy))
      ((kronGrading GX GY).blockSubtensor
        (fun i ↦ finProdFinEquiv (sx i, sy i))) := by sorry
