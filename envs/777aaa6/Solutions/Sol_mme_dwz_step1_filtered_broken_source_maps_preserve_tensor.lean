-- Prove2me | solution 1 for mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:23:00.783537+00:00
-- url     : https://prove2.me/submissions/9818a714-29ee-4583-b09d-45c118a5ba18

import Theorems.Thm_mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
import Theorems.Thm_mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
import Theorems.Thm_mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

open MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    PiTensorProduct.map
        (step1FilteredBrokenSourceMaps K m outer copy)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
      (brokenAddressObj K m outer copy).t := by
  have hRejected :=
    mme_dwz_step1_rejected_singletons_zero_of_coordinate_word_zero
      (K := K) m outer copy
      (mme_dwz_broken_owner_selected_three_words_zero_of_coordinate
        (K := K) m outer copy)
  have hAddress :=
    mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
      (K := K) m outer copy hRejected.1 hRejected.2
  change PiTensorProduct.map
      (fun i ↦ (step1FilteredBrokenAddressMaps K m outer copy i).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) N
          (coarseAddress outer) i))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = _
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  have hProj : PiTensorProduct.map
      (gradedAddressProj (cwSquareCanonicalGrading K 6) N
        (coarseAddress outer))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t =
      (coarseAddressObj K outer).t := by
    exact mme_gradedAddressProj_preserves_kronPow_tensor
      (cwSquareCanonicalGrading K 6) (coarseAddress outer)
  calc
    PiTensorProduct.map (step1FilteredBrokenAddressMaps K m outer copy)
        (PiTensorProduct.map
          (gradedAddressProj (cwSquareCanonicalGrading K 6) N
            (coarseAddress outer))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t) =
      PiTensorProduct.map (step1FilteredBrokenAddressMaps K m outer copy)
        (coarseAddressObj K outer).t :=
      congrArg
        (PiTensorProduct.map (step1FilteredBrokenAddressMaps K m outer copy))
        hProj
    _ = (brokenAddressObj K m outer copy).t := hAddress
