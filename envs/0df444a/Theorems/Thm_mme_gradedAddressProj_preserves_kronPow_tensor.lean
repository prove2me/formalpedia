-- Prove2me | Theorems.Thm_mme_gradedAddressProj_preserves_kronPow_tensor
-- name    : mme_gradedAddressProj_preserves_kronPow_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T14:21:03.924069+00:00
-- url     : https://prove2.me/theorems/2e33d792-6804-4600-94cc-e82cd9fa8fbf
-- title:
--   A graded-address projector preserves the addressed tensor-power block
-- statement:
--   Let an order-three tensor $T$ carry a finite type grading, and prescribe one grading class in every mode and every coordinate of $T^{\otimes R}$. Applying the recursively defined coordinatewise address projector in all three modes maps the tensor of $T^{\otimes R}$ exactly to the tensor of the corresponding ordered graded-address block. This is an equality of tensors, not merely a restriction statement.

import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_gradedAddressProj_preserves_kronPow_tensor
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t) :
    PiTensorProduct.map (gradedAddressProj G R address)
        (T.kronPow R).t =
      (gradedAddressBlock G address).t := by
  sorry
