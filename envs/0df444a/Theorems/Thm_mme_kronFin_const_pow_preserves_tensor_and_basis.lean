-- Prove2me | Theorems.Thm_mme_kronFin_const_pow_preserves_tensor_and_basis
-- name    : mme_kronFin_const_pow_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:57:04.189683+00:00
-- url     : https://prove2.me/theorems/a7081d47-03dc-4036-bb25-c11ea1053fe6
-- title:
--   The ordered constant Kronecker family is exactly the recursive tensor power
-- statement:
--   For a trilinear tensor $T$ and an integer $n$, the recursively ordered Kronecker product of the constant family $(T,\ldots,T)$ is carried to the recursive tensor power $T^{\otimes n}$ by its canonical modewise linear equivalences. These equivalences preserve the literal tensor, not merely its isomorphism class. Moreover, for every mode and every basis word $w$, the ordered product-basis vector is sent exactly to the recursive power-basis vector indexed by the same letters:
--
--   $$
--   F_i(b_{w(0)}\otimes\cdots\otimes b_{w(n-1)})=b_{\operatorname{ofFun}(w)}.
--   $$
--
--   This exact basis formula is the normalization needed when consecutive component fibers of a Coppersmith--Winograd power are regrouped into the fifteen Table-2 component powers.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 (regrouping tensor-power positions into component words), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_const_pow_mode_equiv
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_kron_pow_word_reindex

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronFin_const_pow_preserves_tensor_and_basis
    {K : Type u} [Field K] (T : TensorObj K 3) (n : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (MME.TensorObj.kronFinConstPowModeEquiv T i n).toLinearMap)
        (TensorObj.kronFin n (fun _ ↦ T)).t =
      (T.kronPow n).t ∧
    ∀ (i : Fin 3) {index : Type u} (b : Basis index K (T.V i))
      (w : Fin n → index),
      MME.TensorObj.kronFinConstPowModeEquiv T i n
          (TensorObj.kronFinModePiBasis n (fun _ ↦ T) i
            (fun _ ↦ b) w) =
        MME.DWZComponentRestriction.kronPowModeBasis T i b n
          (MME.DWZComponentRestriction.PowIndex.ofFun n w) := by
  sorry
