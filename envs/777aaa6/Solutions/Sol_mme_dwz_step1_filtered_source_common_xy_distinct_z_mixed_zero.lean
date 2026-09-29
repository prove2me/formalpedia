-- Prove2me | solution 1 for mme_dwz_step1_filtered_source_common_xy_distinct_z_mixed_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:40:14.418558+00:00
-- url     : https://prove2.me/submissions/f432ff4b-6238-4dea-97cd-2d7a1c108380

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
import Definitions.Def_mme_dwz_step1_broken_owner_maps
import Definitions.Def_mme_TypeGrading_kron

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
  classical
  let S : TensorObj K 3 :=
    (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
  let B : Fin k → TensorObj K 3 := fun j ↦
    brokenAddressObj K m (outer j) (copy j)
  let f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i :=
    fun j i ↦ step1FilteredBrokenSourceMaps K m (outer j) (copy j) i
  let U : TensorObj K 3 :=
    { V := fun i ↦ (B (js i)).V i
      t := 0 }
  let bZ := coarseAddressZBasis K (outer (js 2))
  let allowed := addressWordSurvives m (outer (js 2)) (copy (js 2))
  letI : DecidablePred allowed := Classical.decPred _
  let preZ : S.V 2 →ₗ[K] (coarseAddressObj K (outer (js 2))).V 2 :=
    gradedAddressProj (cwSquareCanonicalGrading K 6) N
      (coarseAddress (outer (js 2))) 2
  let selectZ : (coarseAddressObj K (outer (js 2))).V 2 →ₗ[K] U.V 2 :=
    step1FilteredBrokenAddressMaps K m
      (outer (js 2)) (copy (js 2)) 2
  let maps : ∀ i : Fin 3, S.V i →ₗ[K] U.V i :=
    fun i ↦ f (js i) i
  apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
    bZ allowed preZ selectZ maps
  · rfl
  · intro W hW
    change (brokenAddressGrading K m (outer (js 2))
        (copy (js 2))).blockProj 2 0 (bZ W) = 0
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne
      (brokenAddressGrading K m (outer (js 2)) (copy (js 2)))
      2 0 1 (by decide)
    change bZ W ∈ cwBasisGrade bZ
      (fun W' ↦ if allowed W' then 0 else 1) 1
    exact Submodule.subset_span
      ⟨W, by simp only [Set.mem_setOf_eq, if_neg hW], rfl⟩
  · intro W hW
    simpa only [S, B, f, U, bZ, allowed, preZ, selectZ, maps,
      step1FilteredBrokenSourceMaps] using
      hSingletonCross js h01 h02 W hW
