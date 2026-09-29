-- Prove2me | Theorems.Thm_mme_kronFin_modewise_automorphisms_preserve_tensor
-- name    : mme_kronFin_modewise_automorphisms_preserve_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:48:48.220452+00:00
-- url     : https://prove2.me/theorems/b6844cc8-5db4-4034-9bad-bd5cc1abbaa2
-- title:
--   Finite Kronecker products preserve simultaneous tensor automorphisms
-- statement:
--   Let T_0,...,T_{n-1} be order-d tensors over a field. Suppose each factor has one simultaneous family of modewise linear automorphisms whose tensor action fixes that factor. Then the ordered finite Kronecker product has a simultaneous family of modewise linear automorphisms whose tensor action fixes the complete product exactly. This map-level functoriality supplies the fifteen-factor assembly used in the Table-2 realization of DWZ Claim 5.9.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Claim 5.9; generic tensor-product functoriality used in the fifteen-component standard-form realization.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_kronFin_modewise_automorphisms_preserve_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d)
    (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i)
    (hE : ∀ r,
      PiTensorProduct.map (fun i ↦ (E r i).toLinearMap) (T r).t =
        (T r).t) :
    ∃ F : ∀ i,
        (TensorObj.kronFin n T).V i ≃ₗ[K]
          (TensorObj.kronFin n T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin n T).t =
        (TensorObj.kronFin n T).t := by
  sorry
