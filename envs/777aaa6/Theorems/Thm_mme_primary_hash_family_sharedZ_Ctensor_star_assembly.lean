-- Prove2me | Theorems.Thm_mme_primary_hash_family_sharedZ_Ctensor_star_assembly
-- name    : mme_primary_hash_family_sharedZ_Ctensor_star_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:16:02.005134+00:00
-- url     : https://prove2.me/theorems/ea8ce124-54ed-4dcc-b68f-8d4680ae366c
-- title:
--   Shared-Z C-tensor star assembly for a primary hash family
-- statement:
--   Let a tensor have a three-class grading supported only on the four coupled Coppersmith--Winograd coarse types. Suppose an induced primary hash family selects $A$ fibers, each containing $H$ retained exact-profile addresses. Then the selected part of the $2N$-fold tensor power restricts to a modewise direct sum of $A$ star tensors.
--
--   Inside each star, the $H$ components occupy distinct first- and second-mode grading classes but a single shared third-mode class. Consequently the only nonzero grading blocks are the C-tensor addresses $(h,h,*)$, and the block at $(h,h,*)$ is mutually restrictable with the address-dependent retained tensor block for entry $(a,h)$.
--
--   This is the source-faithful tensor assembly on Coppersmith--Winograd (1990), pp. 270--271. It deliberately does not identify all fine blocks with one fixed tensor and makes no dimension claim; those heterogeneous component identifications are supplied separately.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271, especially the primary hashing construction and the shared third-mode C-tensor fibers; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing

open MME

universe u

theorem mme_primary_hash_family_sharedZ_Ctensor_star_assembly
    {K : Type u} [Field K]
    (N L G A H : ℕ)
    (T : TensorObj K 3) (grading : T.TypeGrading 3)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∃ star : Fin A → TensorObj K 3,
      TensorObj.Restrict (TensorObj.bigAdd star) (T.kronPow (2 * N)) ∧
      ∀ a : Fin A,
        ∃ starGrading : (star a).TypeGrading (H + 1),
          (∀ σ : Fin 3 → Fin (H + 1),
            σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              starGrading.blockTensor σ = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (gradedAddressBlock grading (family.entry (a, h)).1)
              (starGrading.blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  sorry
