-- Prove2me | Theorems.Thm_mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
-- name    : mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:00:20.610378+00:00
-- url     : https://prove2.me/theorems/42ac1288-68da-4132-ace6-845413e55452
-- title:
--   A zero address coordinate survives arbitrary modewise postprocessing
-- statement:
--   For a graded order-three tensor power, fix an address word. If the selected graded component tensor is zero at one coordinate, then projecting the full tensor power to that address and applying arbitrary linear maps in all three modes yields zero.

import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor
import Theorems.Thm_mme_gradedAddressBlock_tensor_eq_zero_of_coordinate

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
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
  sorry
