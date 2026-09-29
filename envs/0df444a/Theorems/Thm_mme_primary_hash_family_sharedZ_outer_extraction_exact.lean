-- Prove2me | Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact
-- name    : mme_primary_hash_family_sharedZ_outer_extraction_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:01:55.438621+00:00
-- url     : https://prove2.me/theorems/f66559a0-d041-4820-b062-17882b4112b3
-- title:
--   Exact tensor and Z-map laws for shared-Z outer extraction
-- statement:
--   For any four-block-supported three-grading and any induced primary hash family, the explicit shared-Z outer maps send the full $2N$-fold tensor power exactly to the direct sum of the outer-fiber stars. Moreover, the third-mode map is literally the sum over outer fibers of their graded-address projectors followed by the corresponding direct-sum slot inclusion. This second equality records the common-Z structure needed to prove that forbidden prescribed-profile words are annihilated.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data

open MME PiTensorProduct BigOperators

universe u
set_option autoImplicit false
set_option maxHeartbeats 1200000

open CoupledCTensorPackaging

theorem mme_primary_hash_family_sharedZ_outer_extraction_exact
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0) :
    PiTensorProduct.map (outerExtractionMap grading family)
        (T.kronPow (2 * N)).t =
      (TensorObj.bigAdd (starObj grading family)).t ∧
    outerExtractionMap grading family 2 =
      ∑ a : Fin A,
        (gradedBigAddSlot A (starObj grading family) a 2).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family a (firstFiberIndex family)) 2) := by
  sorry
