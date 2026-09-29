-- Prove2me | solution 1 for mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:09:28.989297+00:00
-- url     : https://prove2.me/submissions/f187e29a-18dc-4489-a537-d4b6eff3a011

import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Theorems.Thm_mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
import Theorems.Thm_mme_dwz_step1_filtered_source_distinct_xy_mixed_zero

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem solution
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
  classical
  let S : TensorObj K 3 :=
    (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
  let B : Fin k → TensorObj K 3 := fun j ↦
    brokenAddressObj K m (outer j) (copy j)
  let f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i :=
    fun j i ↦ step1FilteredBrokenSourceMaps K m (outer j) (copy j) i
  apply mme_tensor_family_direct_sum_restrict_of_mixed_maps S B f
  · intro j
    simpa only [S, B, f] using hDiagonal j
  · intro js hnonconstant
    by_cases h01 : js 0 = js 1
    · have h02 : js 0 ≠ js 2 := by
        intro h02
        apply hnonconstant (js 0)
        funext i
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h02.symm
      simpa only [S, B, f] using
        mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
          (K := K) outer copy hSingletonCross js h01 h02
    · simpa only [S, B, f] using
        mme_dwz_step1_filtered_source_distinct_xy_mixed_zero
          (K := K) outer copy hXYOwner js h01
