-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
-- name    : mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:23:52.5778+00:00
-- url     : https://prove2.me/theorems/3d0ded51-2a81-493f-98b1-8e6db9a02e33
-- title:
--   Step-1-filtered broken owners form a direct-sum restriction
-- statement:
--   A finite family of Step-1-filtered broken owners is a restriction of the square CW power whenever coarse support identifies the X/Y owner, every diagonal owner map preserves its tensor, and every surviving singleton Z word kills a distinct Z owner sharing that X/Y owner.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Steps 1 and 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress (outer (js i)) i r) ≠ 0) →
      js 0 = js 1)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map
          (step1FilteredBrokenSourceMaps K m (outer j) (copy j))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
        (brokenAddressObj K m (outer j) (copy j)).t)
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
      PiTensorProduct.map (Function.update maps 2 selectedZ) S.t = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        brokenAddressObj K m (outer j) (copy j)))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by
  sorry
