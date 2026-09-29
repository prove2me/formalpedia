-- Prove2me | Theorems.Thm_mme_gradedAddressBlock_tensor_eq_zero_of_coordinate
-- name    : mme_gradedAddressBlock_tensor_eq_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T14:28:02.325466+00:00
-- url     : https://prove2.me/theorems/32c3e6ad-06f5-4f90-99af-6a793dd2881f
-- title:
--   One zero coordinate annihilates an ordered graded-address tensor
-- statement:
--   For an ordered graded-address block inside $T^{\otimes R}$, suppose the one-coordinate tensor block selected at some position $r$ is zero. Then the tensor of the entire address block is zero. The result records the elementary but useful fact that one zero factor annihilates the recursively ordered Kronecker product.

import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_gradedAddressBlock_tensor_eq_zero_of_coordinate
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (r : Fin R)
    (hr : G.blockTensor (fun i ↦ address i r) = 0) :
    (gradedAddressBlock G address).t = 0 := by
  sorry
