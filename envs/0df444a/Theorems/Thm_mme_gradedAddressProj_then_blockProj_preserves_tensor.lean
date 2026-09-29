-- Prove2me | Theorems.Thm_mme_gradedAddressProj_then_blockProj_preserves_tensor
-- name    : mme_gradedAddressProj_then_blockProj_preserves_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:13:51.25234+00:00
-- url     : https://prove2.me/theorems/11da80e5-fc0b-4838-9ee1-55119d1b83c4
-- title:
--   Address projection followed by a secondary block projection preserves the selected tensor
-- statement:
--   Let $T^{\otimes R}$ first be projected to an ordered graded-address block $T[a]$, and let $T[a]$ carry a second finite grading. For any secondary multi-type $\sigma$, composing the first address projector with the secondary block projector in every mode maps the original tensor power exactly to the tensor of the $\sigma$-block of $T[a]$. Thus two successive block selections may be represented by one family of mode maps from the original power.

import Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor
import Definitions.Def_mme_block_subtensor

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_gradedAddressProj_then_blockProj_preserves_tensor
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R q : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (H : (gradedAddressBlock G address).TypeGrading q)
    (sigma : Fin 3 → Fin q) :
    PiTensorProduct.map
        (fun i ↦ (H.blockProj i (sigma i)).comp
          (gradedAddressProj G R address i))
        (T.kronPow R).t =
      (H.blockSubtensor sigma).t := by
  sorry
