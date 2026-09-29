-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
-- name    : mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:33:35.246078+00:00
-- url     : https://prove2.me/theorems/974ffad0-c020-41f8-926a-45278517d267
-- title:
--   A surviving Z-word expansion kills a distinct common-X/Y owner
-- statement:
--   Let a family of broken square-CW address tensors be equipped with the Step-1 X/Y filters. Fix a mixed triple of family indices whose X and Y modes have the same owner while its Z mode has a distinct owner. Assume that, for every surviving canonical Z-address word, the tensor map obtained by selecting that word in the Z mode is zero. Then the complete unselected mixed tensor map is zero:
--
--   $$\operatorname{map}(f_{j_0}^{X},f_{j_1}^{Y},f_{j_2}^{Z})\bigl((\mathrm{CW}_6\otimes\mathrm{CW}_6)^{\otimes N}\bigr)=0.$$
--
--   This packages the canonical Z-basis expansion used in Additional Zeroing-Out Step 1: rejected words are killed by the grading projector, while surviving words are killed by the supplied singleton-cross certificate.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Steps 1 and 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hSingletonCross : ∀ (js : Fin 3 → Fin k),
      js 0 = js 1 → js 0 ≠ js 2 →
      ∀ W : AddressZWord (outer (js 2)),
      addressWordSurvives m (outer (js 2)) (copy (js 2)) W →
      let S : TensorObj K 3 :=
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
      let maps : ∀ i : Fin 3, S.V i →ₗ[K]
          (brokenAddressObj K m (outer (js i)) (copy (js i))).V i :=
        fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i
      let singleton :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K (outer (js 2))) id {W}
      let selectedZ :=
        (((step1FilteredBrokenAddressMaps K m
            (outer (js 2)) (copy (js 2)) 2).comp singleton).comp
          (gradedAddressProj (cwSquareCanonicalGrading K 6) N
            (coarseAddress (outer (js 2))) 2))
      PiTensorProduct.map (Function.update maps 2 selectedZ) S.t = 0)
    (js : Fin 3 → Fin k) (h01 : js 0 = js 1) (h02 : js 0 ≠ js 2) :
    PiTensorProduct.map
        (fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0 := by
  sorry
