-- Prove2me | solution 1 for mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:04:00.524299+00:00
-- url     : https://prove2.me/submissions/f679468b-10ee-4878-847d-fb2cb34e966a

import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor
import Theorems.Thm_mme_gradedAddressBlock_tensor_eq_zero_of_coordinate

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-- Once one coordinate block tensor is zero, the projected address tensor
remains zero after arbitrary linear postprocessing in every mode. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t n : ℕ}
    (G : T.TypeGrading t)
    (address : Fin 3 → Fin n → Fin t)
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock G address).V i →ₗ[K] W i)
    (r : Fin n)
    (hr : G.blockTensor (fun i ↦ address i r) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp (gradedAddressProj G n address i))
        (T.kronPow n).t = 0 := by
  rw [PiTensorProduct.map_comp,
    LinearMap.comp_apply,
    mme_gradedAddressProj_preserves_kronPow_tensor]
  have hzero : (gradedAddressBlock G address).t = 0 :=
    mme_gradedAddressBlock_tensor_eq_zero_of_coordinate G address r hr
  rw [hzero]
  exact LinearMap.map_zero _
