-- Prove2me | Theorems.Thm_mme_kronPow_modewise_maps_preserve_tensor
-- name    : mme_kronPow_modewise_maps_preserve_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:23:49.403029+00:00
-- url     : https://prove2.me/theorems/1f1cbc49-c015-4d7a-afde-0ae926308567
-- title:
--   Modewise tensor maps preserve every Kronecker power
-- statement:
--   Let $f_i:T_i\to S_i$ be modewise linear maps that send a tensor $t$ exactly to a tensor $s$. Applying $f_i$ independently in every position of an $n$-fold Kronecker power again sends $t^{\otimes n}$ exactly to $s^{\otimes n}$, for every $n\ge 0$. This supplies the tensor-preservation half of powered basis routers used in the laser-method extraction.
-- source:
--   Standard functoriality of tensor products and Kronecker powers.

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_kronPow_modewise_maps_preserve_tensor
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i : Fin d, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t) : ∀ n : ℕ,
    PiTensorProduct.map (fun i ↦ kronPowModeMap i (f i) n)
        (T.kronPow n).t = (S.kronPow n).t := by
  sorry
